-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_4
-- name    : LDPSelect.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:05:12.258351+00:00
-- url     : https://prove2.me/theorems/e883ff32-3225-4bb9-9098-834132badc2f
-- title:
--   Theorem 4 — value of interaction: factor $\min\{a,d,2\}$ on matroids, $2(1+\lceil\log_2\frac{a+1}{2}\rceil)$ in general, a constant gain for $a\ge 66$
-- statement:
--   Let $a\ge1$.
--
--   1. For every matroid $\mathsf M$ with known arrival order and every product prior,
--   $$W^{\mathrm I}_{\mathsf M}\le\min\{a,\,d(\mathsf M),\,2\}\,W^{\mathrm N}_{\mathsf M},$$
--   where $d$ is the density of $\mathsf M$ after its loops are removed; if every element is a loop, both values are $0$.
--   2. For every downward-closed $\mathcal F$ and every product prior,
--   $$W^{\mathrm I}_{\mathcal F}\le 2\Big(1+\Big\lceil\log_2\frac{a+1}{2}\Big\rceil\Big)\,W^{\mathrm N}_{\mathcal F}.$$
--   3. Conversely, for every $a\ge66$ there is a bounded prior on a rank-two uniform matroid $U_{2,n}$ with $0<W^{\mathrm N}<\infty$ and
--   $$W^{\mathrm I}\ge\Big(1+\frac1{5280}\Big)W^{\mathrm N}.$$
--
--   The theorem bounds how much adaptive reporting can be worth: at most a factor of two on matroids, logarithmic in $a$ in general, and bounded away from one already on rank-two uniform matroids.
--
--   **Formalization Note** The arrival order is the order of `Fin n`. In clause 3 the conditions $0<W^{\mathrm N}<\infty$ exclude the degenerate readings $0\ge0$ and $\infty\ge\infty$.
--
--   Differences from the source:
--   - encoding: a = e^ε ≥ 1 (standing assumption) → a real a with 1 ≤ a as a hypothesis; reason: the standing assumption of §2
--   - encoding: a matroid M with known arrival order → M : Matroid (Fin n) with ground set Fin n, users arriving in the order of Fin n; reason: a fixed order is the order of positions
--   - encoding: d, the density of M after its loops are removed → density M: the maximum of |S| / rk(S) over nonempty sets S of non-loops, rk = Mathlib's eRk; reason: the density of the loopless restriction (§9)
--   - encoding: ⌈log₂((a+1)/2)⌉ → Nat.ceil (Real.logb 2 ((a + 1) / 2)); reason: the argument is ≥ 0 for a ≥ 1, where Nat.ceil is the ceiling
--   - reading: there is a prior on a rank-two uniform matroid with W^I ≥ (1 + 1/5280) W^N → ∃ n and a bounded probability prior on U_{2,n} with 0 < W^N < ∞ and (1 + 1/5280) W^N ≤ W^I; reason: the non-degenerate reading: the claim is a strict multiplicative gain; the paper's prior (A.9) is bounded with W^N > 0
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 4, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Supplement_Matroid

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 4, p.2 (pdf p.3).

(1) For every matroid `M` with known arrival order and every product prior,
`W^I_M ≤ min{a, d(M), 2} W^N_M`, where `d` is the density of `M` after its loops are removed; if every
element is a loop, both values are `0`. (2) For every downward-closed `F`,
`W^I_F ≤ 2(1 + ⌈log₂((a+1)/2)⌉) W^N_F`. (3) Conversely, for every `a ≥ 66` there is a prior on a rank-two
uniform matroid with `W^I ≥ (1 + 1/5280) W^N`.

**Formalization Note.** `a ≥ 1` is the standing assumption of §2 (`a = e^ε`). The arrival order is the
order of `Fin n`. A product prior is a family of probability measures with finite means. `density M` is
the density of the non-loops. `⌈·⌉₊` is applied to `log₂((a+1)/2) ≥ 0`. In (3) the rank-two uniform
matroid is `U_{2,n}` for some `n`, and the prior is bounded with `0 < W^N < ∞`, so the inequality is not
met by `W^N = 0` or `W^N = ∞`. -/
theorem theorem_4 :
    (∀ a : ℝ, 1 ≤ a → ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
      ∀ P : Fin n → Measure ℝ≥0, (∀ i, IsProbabilityMeasure (P i)) → IsIntegrablePrior P →
        ((∃ e, ¬ M.IsLoop e) →
          WI a (indepFam M) P ≤
            ENNReal.ofReal (min a (min (density M) 2)) * WN a (indepFam M) P) ∧
        ((∀ e, M.IsLoop e) → WI a (indepFam M) P = 0 ∧ WN a (indepFam M) P = 0)) ∧
    (∀ a : ℝ, 1 ≤ a → ∀ (n : ℕ) (F : Family n), IsDownClosed F →
      ∀ P : Fin n → Measure ℝ≥0, (∀ i, IsProbabilityMeasure (P i)) → IsIntegrablePrior P →
        WI a F P ≤
          ENNReal.ofReal (2 * (1 + (⌈Real.logb 2 ((a + 1) / 2)⌉₊ : ℝ))) * WN a F P) ∧
    (∀ a : ℝ, 66 ≤ a → ∃ (n : ℕ) (P : Fin n → Measure ℝ≥0),
      (∀ i, IsProbabilityMeasure (P i)) ∧ IsBoundedPrior P ∧
      0 < WN a (unifFam 2 n) P ∧ WN a (unifFam 2 n) P < ⊤ ∧
      ENNReal.ofReal (1 + 1 / 5280) * WN a (unifFam 2 n) P ≤ WI a (unifFam 2 n) P) := by sorry

end LDPSelect.Supplement
