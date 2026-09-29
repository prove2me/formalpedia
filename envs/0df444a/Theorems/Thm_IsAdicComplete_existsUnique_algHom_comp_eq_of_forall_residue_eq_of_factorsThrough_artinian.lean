-- Prove2me | Theorems.Thm_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
-- name    : IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a8de5179-2c20-556d-9d06-eecc1c4a6975
-- title:
--   Passing factorisation through Artinian quotients to a complete local ring
-- statement:
--   Let $A_0$ be a commutative ring, $B$ a commutative $A_0$-algebra, and $R$ a noetherian local commutative $A_0$-algebra that is complete with respect to its maximal ideal, and let $\iota\colon B\to R$ be an $A_0$-algebra map. Let $k$ be a field and $\mathrm{res}_R\colon R\to k$ a surjective ring homomorphism whose kernel is the maximal ideal of $R$. Let $W_0$ be a commutative ring equipped with a ring homomorphism $\mathrm{res}_0\colon W_0\to k$ and with algebra structures making $A_0\to W_0\to R$ a scalar tower, such that $\mathrm{res}_R(\,\cdot\,)$ agrees with $\mathrm{res}_0$ on the image of $W_0$ in $R$. Assume the following factorisation hypothesis: for every Artinian local commutative ring $T$ that is a $W_0$-algebra and an $A_0$-algebra with $A_0\to W_0\to T$ a scalar tower, every surjection $\mathrm{res}_T\colon T\to k$ with kernel the maximal ideal of $T$ and with $\mathrm{res}_T\circ(\text{structure map})=\mathrm{res}_0$ on $W_0$, and every $A_0$-algebra map $\varphi\colon B\to T$ with $\mathrm{res}_T\circ\varphi=\mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi\colon R\to T$ with $\mathrm{res}_T\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Then for every $A_0$-algebra map $\varphi\colon B\to R$ with $\mathrm{res}_R\circ\varphi=\mathrm{res}_R\circ\iota$ there is a unique $W_0$-algebra map $\Phi\colon R\to R$ satisfying $\mathrm{res}_R\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$.
--
--   This is the standard passage from a universal property tested on Artinian local quotients to the same property with the complete local ring itself as target, obtained by applying the hypothesis to the quotients $R/\mathfrak m^{n}$ and using completeness. It is used in the treatment of level structures on modular curves, where endomorphisms of a coordinate ring compatible with a closed point are completed to endomorphisms of the completed local ring at that point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem IsAdicComplete.existsUnique_algHom_comp_eq_of_forall_residue_eq_of_factorsThrough_artinian
    (A₀ : Type) [CommRing A₀]
    (B : Type) [CommRing B] [Algebra A₀ B]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : B →ₐ[A₀] R)
    (k : Type) [Field k]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (W₀ : Type) [CommRing W₀]
    (res₀ : W₀ →+* k)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : B →ₐ[A₀] T, (∀ b : B, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : B, Φ (ι b) = φ b)
    (φ : B →ₐ[A₀] R) (hφ : ∀ b : B, resR (φ b) = resR (ι b)) :
    ∃! Φ : R →ₐ[W₀] R, (∀ r : R, resR (Φ r) = resR r) ∧ ∀ b : B, Φ (ι b) = φ b := by sorry
