-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_gamma0Pow
-- name    : ModularCurve.FullLevel.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/cc7db81b-83d0-5803-94e0-5a6237c59adf
-- title:
--   Surjectivity of Γ₀(M')×Γ(ℓ) Weierstrass points along nilpotent thickenings
-- statement:
--   Fix a prime $\ell$ with $3\le\ell$, a nonzero natural number $M'$, and a commutative ring $A_0$. Two compatibility hypotheses are assumed, each quantified over all $A_0$-algebras $T$: that [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) for $\ell$ is preserved when a Weierstrass curve $W$ is replaced by $C\bullet W$ and the data $D=(x_P,y_P,x_Q,y_Q)$ by its variable-change transform $D.\mathrm{variableChange}\,C$; and that [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $(p,k)$ is preserved when $W$ is replaced by $C\bullet W$ and $h\in T[X]$ by `kernelVariableChangeDeg` $C$ (`gamma0PowDeg` $p\,k$) $h$. Let $B,T$ be $A_0$-algebras and $\pi:B\to T$ a surjective $A_0$-algebra map whose kernel satisfies $(\ker\pi)^n=0$ for some $n$, and suppose $\ell$ and $M'$ are units in $T$. The assertion is that the map induced by $\pi$ on the points of the moduli datum attached to the level component $\Gamma_0$-power $\times$ (level-$\ell$ $\times$ trivial) is surjective. Concretely, points over a ring are variable-change equivalence classes of tuples consisting of a Weierstrass curve $W$ with $\Delta(W)$ a unit, a family $h_p$ of polynomials indexed by the prime factors $p$ of $M'$ with `IsGamma0PowAt` $W\,p\,(M'.\mathrm{factorization}\,p)\,(h_p)$, and a quadruple $D$ which is a level-$\ell$ structure on $W$ (both points satisfy the affine equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and the two independence elements $\prod_{a=1}^{(\ell-1)/2}\bigl(x\,(\Psi^2_a)(x_0)-(\Phi_a)(x_0)\bigr)$ are units in both orders), together with a trivial third slot.
--
--   This is the infinitesimal lifting (formal smoothness) property of the moduli problem of Weierstrass curves with unit discriminant carrying a $\Gamma_0(M')$-structure given by prime-power generator-kernel polynomials and a full level-$\ell$ structure: every point over $T$ lifts to a point over any nilpotent thickening $B$ on which $\pi$ is surjective. It feeds the identification of the completed local rings of the associated moduli package with a power series ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_gamma0Pow
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    {B T : Type} [CommRing B] [CommRing T] [Algebra A₀ B] [Algebra A₀ T]
    (π : B →ₐ[A₀] T) (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (hℓT : IsUnit ((ℓ : ℕ) : T)) (hM'T : IsUnit ((M' : ℕ) : T)) :
    Function.Surjective ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.map π) := by sorry
