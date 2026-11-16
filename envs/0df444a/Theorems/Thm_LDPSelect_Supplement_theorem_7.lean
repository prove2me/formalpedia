-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_7
-- name    : LDPSelect.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:07:23.099159+00:00
-- url     : https://prove2.me/theorems/1fc6bd42-7e6b-457b-b558-f2d03d9cc79c
-- title:
--   Theorem 7 — density law for matroids: $\max\{1/d,\,a/(2(a+\bar d-1))\}\le\inf W^{\mathrm N}/M\le\inf W^{\mathrm I}/M\le\min\{1,a/d\}$
-- statement:
--   Let $\mathsf M$ be a loopless matroid on a nonempty ground set, with rank function $\operatorname{rk}$, density $d=\max_{S\ne\emptyset}|S|/\operatorname{rk}(S)$ and $\bar d=\max\{d,2\}$, and let $a\ge1$. Then
--   $$\max\Big\{\frac1d,\ \frac{a}{2(a+\bar d-1)}\Big\}\le\inf_X\frac{W^{\mathrm N}_{\mathsf M}(X)}{\mathbb E[\max_{I\in\mathcal I}X(I)]}\le\inf_X\frac{W^{\mathrm I}_{\mathsf M}(X)}{\mathbb E[\max_{I\in\mathcal I}X(I)]}\le\min\Big\{1,\ \frac ad\Big\}.$$
--
--   The density replaces the scale $n/k$ of the uniform matroid $U_{k,n}$: for every matroid the private optimum captures a fraction of the prophet's value of order $\min\{1,a/d\}$.
--
--   **Formalization Note** The infima run over product priors with integrable values and $0<\mathbb E[\max_{I\in\mathcal I}X(I)]<\infty$, the same set for both models.
--
--   Differences from the source:
--   - encoding: a = e^ε ≥ 1 (standing assumption) → a real a with 1 ≤ a as a hypothesis; reason: the standing assumption of §2
--   - encoding: a loopless matroid M → M : Matroid (Fin n), 0 < n, ground set Fin n, no element a loop; reason: d is a maximum over nonempty sets, so the ground set is nonempty
--   - encoding: d = max_{S≠∅} |S|/rk(S) → density M (the maximum over nonempty sets of non-loops, which for a loopless matroid is every nonempty set); reason: one definition shared with Theorem 4
--   - encoding: inf_X W(X) / M(X) → ratioN / ratioI: the infimum in [0, ∞] over probability priors with finite means and 0 < M < ∞; reason: the priors for which the ratio is defined; on them it is a quotient of finite numbers with positive denominator
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 7, p.3 (pdf p.4)

import Mathlib
import Definitions.Def_LDPSelect_Supplement_Matroid
import Definitions.Def_LDPSelect_Supplement_Ratios

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 7, p.3 (pdf p.4).

For a loopless matroid `M` with rank function `rk`, density `d = max_{S≠∅} |S|/rk(S)` and
`d̄ = max{d, 2}`,
`max{1/d, a/(2(a + d̄ − 1))} ≤ inf_X W^N_M(X)/E[max_{I∈I} X(I)] ≤ inf_X W^I_M(X)/E[max_{I∈I} X(I)] ≤ min{1, a/d}`.

**Formalization Note.** The ground set is a nonempty `Fin n` (`d` is a maximum over nonempty sets) with
`M.E = Set.univ`. `a ≥ 1` is the standing assumption of §2. For a loopless matroid `density M` is the
paper's `d`. The infima are `ratioN`, `ratioI` over the same priors (probability, finite means,
`0 < M_M < ∞`). -/
theorem theorem_7 (n : ℕ) (hn : 0 < n) (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (hloop : ∀ e, ¬ M.IsLoop e) (a : ℝ) (ha : 1 ≤ a) :
    ENNReal.ofReal (max (1 / density M) (a / (2 * (a + max (density M) 2 - 1)))) ≤
        ratioN a (indepFam M) ∧
      ratioN a (indepFam M) ≤ ratioI a (indepFam M) ∧
      ratioI a (indepFam M) ≤ ENNReal.ofReal (min 1 (a / density M)) := by sorry

end LDPSelect.Supplement
