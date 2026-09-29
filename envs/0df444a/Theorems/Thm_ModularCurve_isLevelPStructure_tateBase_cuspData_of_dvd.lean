-- Prove2me | Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd
-- name    : ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/591fc1c7-8163-5ede-8799-fcc654cd1aa7
-- title:
--   Cusp of Tate(qⁿ) gives a level-ℓ structure when ℓ ∣ n
-- statement:
--   Let $R$ be a commutative ring, $\ell$ a prime with $\ell \neq 2$ whose image in $R$ is a unit, and $n$ a nonzero natural number divisible by $\ell$. Let $\zeta \in R^{\times}$ satisfy $\sum_{i=0}^{\ell-1} (\zeta^{n/\ell})^{i} = 0$ in $R$, so that $\zeta^{n/\ell}$ is a primitive $\ell$-th root of unity in the strong sense. Consider the Weierstrass curve [`ModularCurve.tateBase R n`](def/ModularCurve_TateSlots.html#L46) over the Laurent series ring $R((q))$: the Tate curve `tateLaurent R` (obtained from the universal Tate power-series curve by coefficient extension) transported along the ring endomorphism `qExpand R n` of $R((q))$ that multiplies the exponent index by $n$, i.e. the Tate curve with parameter $q^{n}$. On it, take the pair of points `cuspData R n ζ ![(n/\ell : ZMod n), 0] ![0, (n/\ell : ZMod n)]`: the first is the toric cusp point `tateToricPoint` with parameter $\zeta^{n/\ell}$ (the second label being $0$), while the second, whose second label $n/\ell$ is nonzero in $\mathrm{ZMod}\,n$, is the non-toric point `nonToricPoint` with toric part $\zeta^{0}$ and $q$-part of index $n/\ell$. The assertion is `IsLevelPStructure` for this data at $\ell$, namely: both coordinate pairs satisfy the affine Weierstrass equation of the curve; both abscissae $x_P, x_Q$ are roots of the polynomial $\mathrm{pre}\Psi_\ell$ of the curve; and both independence elements $\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,\Psi^{2}_{a}(x_P) - \Phi_{a}(x_P)\bigr)$ and $\prod_{a=1}^{(\ell-1)/2}\bigl(x_P\,\Psi^{2}_{a}(x_Q) - \Phi_{a}(x_Q)\bigr)$ are units of $R((q))$.
--
--   This exhibits, in division-polynomial coordinates, the classical full level-$\ell$ structure on the Tate curve with parameter $q^{n}$ given by the pair $(\zeta^{n/\ell}, q^{n/\ell})$ of $\ell$-torsion parameters of the uniformisation $\mathbb{G}_m/q^{n\mathbb{Z}}$, for $\ell$ an odd prime dividing $n$; it generalises the case $n = \ell$ recorded in [`ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp). It is used in the construction of points on full level-$\ell$ modular curves over Laurent series rings with prescribed $j$-invariant, via [`ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra`](thm.html#ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd
    {R : Type u} [CommRing R] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : IsUnit (ℓ : R))
    (n : ℕ) [NeZero n] (hn : ℓ ∣ n)
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range ℓ, ((ζ : R) ^ (n / ℓ)) ^ i = 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R n) ℓ
      (ModularCurve.cuspData R n ζ ![((n / ℓ : ℕ) : ZMod n), 0] ![0, ((n / ℓ : ℕ) : ZMod n)]) := by sorry
