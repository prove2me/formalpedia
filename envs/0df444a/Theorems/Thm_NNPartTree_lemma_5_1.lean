-- Prove2me | Theorems.Thm_NNPartTree_lemma_5_1
-- name    : NNPartTree.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:31.601349+00:00
-- url     : https://prove2.me/theorems/b54b6a52-bea9-4a1f-be64-c956efeff646
-- title:
--   Lemma 5.1, p.16 — Cheeger-style rounding: $\mathrm{err}\le 64\sqrt{R_S(F)}$ and $\mathrm{bal}\ge 1/(640\gamma)$
-- statement:
--   For any measurable $F:\mathbb R^d\to\mathbb R$ and any law $S$ on pairs in $\mathbb R^d\times\mathbb R^d$, with positive variance on $S_Y$, there is a threshold $\theta$ such that $g_{F,\theta}(x)=\mathrm{sign}(F(x)-\theta)$ satisfies
--   $$\mathrm{err}_S(g_{F,\theta})\le 64\sqrt{R_S(F)}\quad\text{and}\quad\mathrm{bal}_S(g_{F,\theta})\ge\frac1{640\,\gamma(F;S_Y)}.$$
--
--   A real-valued function of low energy and bounded kurtosis therefore yields a sparse, balanced threshold cut.
--
--   Differences from the source:
--   - encoding: O(√R), Ω(1/γ) → constants 64 and 640; reason: the constants of the proof, p.45; they imply the printed bounds
--   - encoding: any F → F measurable with Var > 0; each bound conditional on the integrability of its own quantity; reason: R and γ are 0/0 on zero variance, and when R or γ is infinite the printed bound is trivial while the Lean integral would read 0; the other bound is still claimed, for the same θ
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 5.1, p.16; proof pp.42–45, constants p.45

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Lemma 5.1** (Cheeger-style Rounding), p.16; proof pp.42–45. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

For any `F` and any law `S` on pairs there is `θ` with `err_S(g_{F,θ}) ≤ 64 √R_S(F)` and
`bal_S(g_{F,θ}) ≥ 1/(640 γ(F; S_Y))`. The constants `64` and `640` are those of the proof (p.45).

**Formalization Note.** `Var_{S_Y}[F] > 0` is assumed, without which `R` and `γ` are `0/0`. Each bound is conditional on the
integrability of its own quantity: when `R` or `γ` is infinite the printed bound is trivial, while the Lean integral would read `0`. So the
other bound is still claimed, for the same `θ`. -/
theorem lemma_5_1 {d : ℕ} (S : Measure (Pt d × Pt d)) [IsProbabilityMeasure S] (F : Pt d → ℝ)
    (hF : Measurable F) (hvar : 0 < varOn (marginalY S) F) :
    ∃ θ : ℝ,
      (Integrable (fun z : Pt d × Pt d => (F z.1 - F z.2) ^ 2) S →
        err S (thresholdCut F θ) ≤ 64 * Real.sqrt (energy S F)) ∧
      (Integrable (fun y => F y ^ 4) (marginalY S) →
        1 / (640 * kurtosis (marginalY S) F) ≤ bal S (thresholdCut F θ)) := by sorry

end NNPartTree
