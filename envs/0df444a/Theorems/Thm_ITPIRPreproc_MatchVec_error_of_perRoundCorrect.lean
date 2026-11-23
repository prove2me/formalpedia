-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_error_of_perRoundCorrect
-- name    : ITPIRPreproc.MatchVec.error_of_perRoundCorrect
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:51:41.169149+00:00
-- url     : https://prove2.me/theorems/7019b981-589e-4244-99b7-3d58a0723033
-- title:
--   Per-round error gives the $T\delta$ adaptive correctness bound
-- statement:
--   Suppose that in the adaptive experiment of §3, for every database and every measurable adaptive adversary, each round $j$ satisfies
--   $$
--   \Pr[y_j\ne D[i_j]]\le\delta,
--   $$
--   where output $\bot$ is included as a failure. Then for every number $T$ of retrieval protocols,
--   $$
--   \Pr\big[\exists j\in\{1,\ldots,T\}:y_j\ne D[i_j]\big]\le T\delta.
--   $$
--
--   This is the union bound used at the end of the correctness proof of Lemma 4.2; independence between different rounds is not required.
--
--   **Formalization Note** The induction splits the first $T+1$ protocols into the first $T$ protocols and the single new record, using subadditivity of `tapeLaw`. No measurability proof for the failure event is needed for subadditivity.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 4.2 correctness proof, printed p.15 (PDF p.17), final union bound over $T$ retrieval protocols; §3 correctness definition, printed p.10 (PDF p.12).

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open scoped ENNReal

/-- If every individual retrieval has failure probability at most `δ`, then over `T` retrieval
protocols the probability of at least one failure is at most `T δ`. -/
theorem error_of_perRoundCorrect (S : Scheme) (n lam : ℕ) (δ : ℝ≥0∞)
    (h : PerRoundCorrect S n lam δ) :
    Correct S n lam (fun T => (T : ℝ≥0∞) * δ) := by sorry
