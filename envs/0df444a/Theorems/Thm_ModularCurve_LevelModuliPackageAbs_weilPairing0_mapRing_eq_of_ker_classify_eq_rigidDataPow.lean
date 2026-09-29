-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
-- name    : ModularCurve.LevelModuliPackageAbs.weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0ba19cb6-aea7-5ff2-8d4d-ca1ba145c12f
-- title:
--   Weil pairing determined by the kernel of `classify`
-- statement:
--   Let $A$ be a commutative ring, $\ell$ a prime with $3\le\ell$ and $(\ell:A)$ a unit, $M'$ a nonzero natural number and $q$ a prime. Assume given the two variable-change stability hypotheses `hℓ` (for every $A$-algebra $T$, Weierstrass curve $W/T$, variable change $C$ and `LevelPData` $D$, if $D$ is a Katz level-$\ell$ structure on $W$ — both points satisfy the affine equation, both abscissae are roots of $W.\mathrm{pre}\Psi_\ell$, and both independence elements `indepElt` are units — then $D.\mathrm{variableChange}\,C$ is one on $C\bullet W$) and `hM` (the same stability for `IsGamma0PowAt` under `kernelVariableChangeDeg`), together with group laws $\mathcal G$ on projective Weierstrass models over $A$-algebras and a level transport $\mathcal T$ for Drinfeld $q$-bases. Write $R=$ `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯`, the rigid Weierstrass data whose raw objects over an $A$-algebra $T$ consist of a Weierstrass curve with unit discriminant together with a $\Gamma_0$-type tuple of kernel polynomials for the prime powers of $M'$, a Katz level-$\ell$ datum and a Drinfeld level-$q$ pair, all satisfying the corresponding level conditions, and whose points $R.\mathrm{Pt}\,T$ are the quotient by the variable-change relation. Let $P_0$ be an abstract representing package for the associated moduli datum, so that each point $x$ over $T$ has a unique classifying $A$-algebra map $P_0.\mathrm{classify}\,x\colon B_0\to T$ carrying the universal point to $x$. Let $K$ be a field over $A$, let $\zeta\in A$ have image in $K$ a primitive $\ell$-th root of unity, and let $\Omega$ be an algebraically closed field which is a $K$-algebra compatibly with $A$. Let $x_1,x_2\in R.\mathrm{Pt}\,K$ have equal kernels of the underlying ring homomorphisms of their classifying maps, and let $y_1,y_2$ be raw objects over $K$ representing $x_1,x_2$. Put $z_i=R.\mathrm{mapRing}$ of $y_i$ along the $A$-algebra map $K\to\Omega$, each $z_i$'s curve being elliptic since its discriminant is a unit. Then the two values $\mathrm{weilPairing0}$ of the curve of $z_i$ over $\Omega$ at exponent $\ell$, evaluated on the points of the base change to $\Omega$ obtained from the coordinates $x_P,y_P$ and $x_Q,y_Q$ of the Katz level-$\ell$ component $z_i.\mathrm{level}.2.1$ (each taken via `toPoint`, which returns the affine point if it is nonsingular and $0$ otherwise), agree as elements of $\Omega$.
--
--   The statement expresses the Weil pairing of the Katz level-$\ell$ basis as an invariant of the prime of the representing ring $B_0$ through which a field-valued point factors, rather than of the point itself; the pairing is read on base-changed representatives over an algebraically closed field. It is used in the determinant computation [`ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow`](thm.html#ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow) for the full-level moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

theorem ModularCurve.LevelModuliPackageAbs.weilPairing0_mapRing_eq_of_ker_classify_eq_rigidDataPow
    (A : Type) [CommRing A] (ℓ M' q : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) [NeZero M'] [Fact q.Prime]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (K : Type) [Field K] [Algebra A K] (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) ℓ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x₁ x₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw K)
    (hy₁ : (Quot.mk _ y₁ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₁)
    (hy₂ : (Quot.mk _ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₂) :
    letI z₁ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁
    letI z₂ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂
    letI _ : (z₁.curve).IsElliptic := ⟨z₁.isUnit_Δ⟩
    letI _ : (z₂.curve).IsElliptic := ⟨z₂.isUnit_Δ⟩
    ((weilPairing0 z₁.curve Ω (ℓ : ℤ)
        (toPoint ((z₁.curve).baseChange Ω) z₁.level.2.1.xP z₁.level.2.1.yP)
        (toPoint ((z₁.curve).baseChange Ω) z₁.level.2.1.xQ z₁.level.2.1.yQ) : Ωˣ) : Ω) =
      ((weilPairing0 z₂.curve Ω (ℓ : ℤ)
        (toPoint ((z₂.curve).baseChange Ω) z₂.level.2.1.xP z₂.level.2.1.yP)
        (toPoint ((z₂.curve).baseChange Ω) z₂.level.2.1.xQ z₂.level.2.1.yQ) : Ωˣ) : Ω) := by sorry
