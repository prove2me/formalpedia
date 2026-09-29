-- Prove2me | Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
-- name    : ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/bce4a0b4-55f9-53c1-8834-fb23d20ff401
-- title:
--   Mazur's cusp gives a level-p structure on Tate(qᵖ)
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime with $5 \le p$ such that $p$ is a unit in $R$; let $\zeta \in R^\times$ satisfy $\sum_{i<p} \zeta^i = 0$, and let $a \in \mathbb{Z}/p$ with $a \ne 0$. Work with the Weierstrass curve [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46) over the Laurent series $R((q))$, namely the Tate curve `tateLaurent R` pushed forward along the ring homomorphism `qExpand R p`, which multiplies Hahn-series exponents by $p$ (so the curve $\mathrm{Tate}(q^p)$). The level-$p$ data `cuspData R p ζ ![a,0] ![0,1]` consists of the two points produced by `cuspPoint`: since the second entry of $![a,0]$ vanishes, $P$ is the toric point `tateToricPoint R p (ζ ^ a.val)`, and since the second entry of $![0,1]$ does not, $Q$ is `nonToricPoint R p 1 1`, the point of parameter $q$. The conclusion is that this pair satisfies `IsLevelPStructure`, i.e.: $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of the curve; the polynomial $\mathrm{preΨ}\,p$ of the curve vanishes at $x_P$ and at $x_Q$; and both elements $\mathrm{indepElt} = \prod_{b=1}^{(p-1)/2}\bigl(x_Q\,\Psi_b^2(x_P) - \Phi_b(x_P)\bigr)$ and the same product with $P$ and $Q$ interchanged are units in $R((q))$.
--
--   This is the statement, for primes $p \ge 5$, that Mazur's cusp $(\mathrm{Tate}(q^p), \zeta^a, q)$ is a genuine point of the full level-$p$ moduli problem in division-polynomial coordinates. It serves as a test object at which level-$p$ forms can be evaluated, and is used by the results on $q$-expansions of Katz modular forms, among them [`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le) and [`ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff`](thm.html#ModularForm.exists_katzModularForm_qExpansion_eq_C_of_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp_of_five_le
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R))
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (a : ZMod p) (ha : a ≠ 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
      (ModularCurve.cuspData R p ζ ![a, 0] ![0, 1]) := by sorry
