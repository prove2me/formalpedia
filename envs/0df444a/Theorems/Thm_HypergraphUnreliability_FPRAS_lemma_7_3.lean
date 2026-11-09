-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_7_3
-- name    : HypergraphUnreliability.FPRAS.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:47.753214+00:00
-- url     : https://prove2.me/theorems/f5871a80-8ecb-4890-9fbf-a500f7d2b552
-- title:
--   Lemma 7.3 — Fixed-bit categorical draw error
-- statement:
--   **One draw.** For a rational categorical distribution with at most $C$ categories, the $q$-bit draw of §7.3 has total variation error at most $C2^{-q}$.
--
--   **One sample.** Assume the standing context, positive rational rates, $\Lambda$ the minimum cut, $h\ge0$, $h\sum_e r_e\le1$ and $q\ge1$. Then the pair and terminal state of one fixed-bit sample, with the initial pair and $L$ updates, are within
--   $$[N+L(2m+2)]\,2^{-q}$$
--   of those with exact draws.
--
--   **The printed statement.** For the parameters of the common-probability algorithm, with $q$ from (7.5), this error is at most $\varepsilon/(128N)$.
--
--   The general bound specializes to (7.5) and to the weighted choice (9.9).
--
--   Differences from the source:
--   - generalization: error over the initial pair and $L$ updates for the common parameters → in addition the accumulated bound $[N+L(2m+2)]2^{-q}$ for general parameters; reason: it is the bound written in the proof and used at (9.9); the printed statement is the third clause, unchanged
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 7.3, p. 10; (7.5), p. 10; (9.9), p. 14

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_EulerSampler
import Definitions.Def_HypergraphUnreliability_FPRAS_CommonAlgorithm

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 7.3, p. 10, in three layers.

One draw: for a rational categorical list with nonnegative masses summing to one and at most `C`
categories, the `q`-bit draw has total variation error at most `C 2^{-q}`.

One sample, for general parameters: the pair and terminal state of one fixed-bit sample are within
`[N + L(2m+2)] 2^{-q}` of the exact-draw law (the bound specializing to (7.5) and to (9.9)).

The printed statement, for the common-probability parameters: this error is at most `ε/(128 N)`. -/
theorem lemma_7_3 :
    (∀ {α : Type} [Fintype α] (cats : List (ℚ × α)) (d : α) (q C : ℕ),
      (∀ c ∈ cats, 0 ≤ c.1) → (cats.map Prod.fst).sum = 1 → cats.length ≤ C →
      tvDist (fixedBitLaw cats d q) (fun y => ((categoryMass cats y : ℚ) : ℝ)) ≤
        (C : ℝ) * (1 / 2 : ℝ) ^ q) ∧
    (∀ {n m : ℕ} (P : SamplerParams n m), P.H.Standing → (∀ e, 0 < P.r e) →
      P.Λ = P.H.minCut P.r → 0 ≤ P.h → P.h * ∑ e, P.r e ≤ 1 → 1 ≤ P.q →
      tvDist P.sampleLaw P.exactSampleLaw ≤
        (((n.choose 2 : ℕ) : ℝ) + (P.L : ℝ) * (2 * (m : ℝ) + 2)) * (1 / 2 : ℝ) ^ P.q) ∧
    (∀ x : CommonInstance, x.Valid → x.IsSamplingCase →
      tvDist x.params.sampleLaw x.params.exactSampleLaw ≤ ((x.ε.val / (128 * x.N) : ℚ) : ℝ)) := by sorry

end HypergraphUnreliability.FPRAS
