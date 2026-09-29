-- Prove2me | Theorems.Thm_ModularCurve_modularFunctionFieldBar_le
-- name    : ModularCurve.modularFunctionFieldBar_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/f9be3be0-eb4f-5a52-bc92-25de9db4eaa2
-- title:
--   Base change preserves the degeneracy inclusion ̄ F_N≤̄ F_M
-- statement:
--   Let $N$ and $M$ be natural numbers, both nonzero, and suppose $N \mid M$. For a nonzero natural number $n$, [`ModularCurve.modularFunctionFieldFull n`](def/ModularCurve_X0.html#L305) denotes the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set `divisorExpansions n` of Laurent series (the $q$-expansions attached to the divisors of $n$), and [`ModularCurve.modularFunctionFieldBar n`](def/ModularCurve_ArithmeticGalois.html#L111) is its base change to $\overline{\mathbb{Q}}$: namely [`ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldFull n)`](def/ModularCurve_LaurentCoeff.html#L103), the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of [`ModularCurve.modularFunctionFieldFull n`](def/ModularCurve_X0.html#L305) under the coefficientwise embedding `coeffEmb (AlgebraicClosure ℚ)` of $\mathbb{Q}((q))$ into $\overline{\mathbb{Q}}((q))$. The assertion is the inequality $$\mathrm{modularFunctionFieldBar}\,N \le \mathrm{modularFunctionFieldBar}\,M$$ in the lattice of intermediate fields of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$, i.e. every element of the base-changed field attached to $N$ lies in the one attached to $M$.
--
--   This is the degeneracy inclusion $\overline F_N \subseteq \overline F_M$ for $N \mid M$ in the $q$-expansion model of the modular function fields over $\overline{\mathbb{Q}}$, the analogue over the algebraic closure of the inclusion of function fields coming from the degeneracy maps $X_0(M) \to X_0(N)$. It is used in the construction of the characteristic-$p$ models, in [`ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem`](thm.html#ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem) and [`ModularCurve.CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem`](thm.html#ModularCurve.CharPModel.exists_monic_eval2_affineBaseInf_eq_zero_of_mem_modularLocalized_of_forall_inv_jBar_mem), and in [`ModularCurve.isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd`](thm.html#ModularCurve.isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularFunctionFieldBar_le.lean

import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.modularFunctionFieldBar_le (N : ℕ) [NeZero N] {M : ℕ} [NeZero M] (h : N ∣ M) : ModularCurve.modularFunctionFieldBar N ≤ ModularCurve.modularFunctionFieldBar M := by sorry
