-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel
-- name    : ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/7a63d564-8448-53f3-b962-5cfb7f3fb6bf
-- title:
--   Relabelling by g then g' with gg' ≡ 1 (mod q)
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws assigning, to every $A$-algebra $T$, every projective Weierstrass model $W$ over $T$ and every proof that $\Delta_W$ is a unit, a relative group law on the projective model of $W$. Assume: $\mathcal G$ is chord–tangent, i.e. each member law admits an evaluation exhibiting it as the law on points; $\mathcal G$ has the origin as identity, i.e. for each member law there is a ring homomorphism out of the origin chart ring realising the unit section as an origin chart section and killing $x/y$ and $z/y$; and that variable changes and coefficient homomorphisms are realised on graded coordinate rings, namely for each $W$ over an $A$-algebra $T$ and each variable change $C$ there is a graded ring homomorphism $\mathrm{projModelGradingCR}(W) \to \mathrm{projModelGradingCR}(C \cdot W)$ fixing constants, acting on $X_0, X_1, X_2$ by the usual $(u,r,s,t)$ formulas and pulling back the irrelevant ideal, and likewise for $W \mapsto W.\mathrm{map}\, f$ along an $A$-algebra map $f : T \to T'$, where constants go to their images and each $X_i$ to $X_i$. Let $q \ge 2$, let $T$ be an $A$-algebra, $W$ a projective Weierstrass model over $T$, and $x = (x.\mathrm{curve}; P, Q)$ a raw Drinfeld pair over $T$ with $\Delta_{x.\mathrm{curve}}$ a unit, such that $x$ is of level $q$ for $\mathcal G$ over $W$: $x.\mathrm{curve} = W$ and $P, Q$ form a Drinfeld basis of level $q$ for the associated member law. Then, for integer $2 \times 2$ matrices $g, g'$ whose product reduces to the identity matrix over $\mathbb Z/q$, relabelling $x$ by $g$ and then by $g'$ — where relabelling by a matrix keeps the curve and replaces $(P,Q)$ by the $\mathbb Z$-linear combinations $(g_{00} P + g_{10} Q,\ g_{01} P + g_{11} Q)$ formed with the group law — returns $x$ itself.
--
--   This is the two-sided-inverse step in the relabelling package for full level $q$ structures: it says that relabelling by $g$ and by an inverse of $g$ modulo $q$ are mutually inverse automorphisms of the moduli problem of Drinfeld bases of level $q$. It is used in the construction of the fine moduli data for full level and for the $\Gamma_0$- and $\Gamma_1$-type rigid data built from it; the hypothesis $q \ge 2$ is what makes dependence on $g$ modulo $q$ alone available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (q : ℕ) (hq : 2 ≤ q) (T : Type) [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q W x)
    (g g' : Matrix (Fin 2) (Fin 2) ℤ) (hgg' : (g * g').map (Int.castRingHom (ZMod q)) = 1) :
    ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g'
        (ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x hΔ) hΔ = x := by sorry
