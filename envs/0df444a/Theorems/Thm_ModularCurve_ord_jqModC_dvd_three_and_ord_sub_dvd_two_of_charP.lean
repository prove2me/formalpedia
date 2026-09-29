-- Prove2me | Theorems.Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
-- name    : ModularCurve.ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/e636da1e-1996-5e6b-8fe1-cb2405f85ce8
-- title:
--   Ramification over j=0 and j=1728 divides 3 and 2
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N \ge 1$ be an integer with $p \nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Write $F = \mathrm{modularFunctionFieldFullC}\,K\,N$ for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all the series $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ as $d$ runs over the nonzero divisors of $N$, where $\mathrm{jqModC}\,K = q^{-1}\cdot(\mathrm{eisenstein4}^3\cdot\mathrm{dedekindEtaUnitInv})$ is the $q$-expansion of the modular invariant $j$ with coefficients mapped into $K$. Let $\bar\jmath \in F$ be this series, viewed as an element of $F$. The assertion is that for every place $w$ of $F$ over $K$ — that is, every valuation subring of $F$ that contains $\mathrm{algebraMap}\,K\,F$ of every element of $K$, is not all of $F$, and is a principal ideal ring — with $\mathrm{ord}_w$ the associated integer-valued order function (the negative of the logarithm of the adic valuation attached to $w$): if $\mathrm{ord}_w(\bar\jmath) > 0$ then $\mathrm{ord}_w(\bar\jmath) \mid 3$, and if $\mathrm{ord}_w(\bar\jmath - 1728) > 0$ then $\mathrm{ord}_w(\bar\jmath - 1728) \mid 2$, both divisibilities in $\mathbb{Z}$.
--
--   This is the tame ramification of the covering of the $j$-line by the modular curve of level $N$ in characteristic $p \ge 5$, $p \nmid N$, over the two elliptic points: the ramification index above $j = 0$ divides $3$ and above $j = 1728$ divides $2$. In the form stated, for the full level-$N$ function field and phrased through $\mathrm{ord}_w$, it is the ramification hypothesis used in the degree computations for weight-$2m$ floor divisors and in the dimension bounds for mod $p$ modular forms ([`ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one`](thm.html#ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one), [`ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent`](thm.html#ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent), [`ModularCurve.ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub`](thm.html#ModularCurve.ell_le_dimFormulaCusp_of_forall_eq_weightFloor_sub)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.ord_jqModC_dvd_three_and_ord_sub_dvd_two_of_charP
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      (0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) →
          w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) ∣ 3) ∧
      (0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) →
          w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) ∣ 2) := by sorry
