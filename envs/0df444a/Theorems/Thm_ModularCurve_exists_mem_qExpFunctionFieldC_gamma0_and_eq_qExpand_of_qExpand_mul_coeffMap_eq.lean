-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
-- name    : ModularCurve.exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a03c4590-8bac-59c5-a2dd-bda231f31ca0
-- title:
--   Gauss residues descend from Γ₀(qN) to Γ₀(N)
-- statement:
--   Fix a prime $q$, an integer $N \geq 1$ with $q \nmid N$, a field $L$ of characteristic zero (an algebra over $\mathbb{Q}$) and a valuation subring $A \subseteq L$ whose residue field $\kappa =$ `IsLocalRing.ResidueField A` has characteristic $q$; write $\iota =$ `coeffMap A.subtype` for the coefficientwise map $A((X)) \to L((X))$ and $z \mapsto \bar z$ for the coefficientwise reduction `coeffMap (IsLocalRing.residue A)` onto $\kappa((X))$, and let `qExpand` denote the ring endomorphism of a Laurent series field that multiplies all exponents by $q$ (substitution $X \mapsto X^q$). Let $g$ be a Laurent series over $L$ lying in `laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * N)))`, that is, in the subfield of $L((X))$ generated over $L$ by the coefficientwise images of the subfield of $\mathbb{Q}((X))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where $f, g$ are modular forms of a common weight $k$ on $\Gamma_0(qN)$ with integral $q$-expansions $p_f, p_g$ and the denominator series is nonzero. Suppose given $x, y \in A((X))$ with $\bar y \neq 0$ and `qExpand L q g` $\cdot\, \iota(y) = \iota(x)$, and suppose $r \in \kappa((X))$ satisfies $r \cdot \bar{y'} = \bar{x'}$ for every pair $x', y' \in A((X))$ with $\bar{y'} \neq 0$ and `qExpand L q g` $\cdot\, \iota(y') = \iota(x')$. Then there exists $e$ in `qExpFunctionFieldC κ (CongruenceSubgroup.Gamma0 N)`, the subfield of $\kappa((X))$ generated over $\kappa$ by such ratios of integral $q$-expansions of forms on $\Gamma_0(N)$, with $r =$ `qExpand κ q e`.
--
--   This is the level-lowering step at the prime $q$ for Gauss-type residues: a residue of the $X \mapsto X^q$ substitution of a function on $\Gamma_0(qN)$, taken with respect to a valuation subring with residue characteristic $q$, is again such a substitution, but of a function in the reduced function field at the lower level $N$. It is used in the analysis of the full-level modular curve, in particular by the lemmas computing the pullback of level automorphisms under reduction ([`ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq) and its variants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq.lean

import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
    (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    {L : Type} [Field L] [Algebra ℚ L] (A : ValuationSubring L) [CharP (IsLocalRing.ResidueField A) q]
    (g : LaurentSeries L)
    (hg : g ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * N))))
    (x y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : qExpand L q g * coeffMap A.subtype y = coeffMap A.subtype x)
    (r : LaurentSeries (IsLocalRing.ResidueField A))
    (hr : ∀ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 →
      qExpand L q g * coeffMap A.subtype y' = coeffMap A.subtype x' →
        r * coeffMap (IsLocalRing.residue A) y' = coeffMap (IsLocalRing.residue A) x') :
    ∃ e : LaurentSeries (IsLocalRing.ResidueField A),
      e ∈ qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 N) ∧
        r = qExpand (IsLocalRing.ResidueField A) q e := by sorry
