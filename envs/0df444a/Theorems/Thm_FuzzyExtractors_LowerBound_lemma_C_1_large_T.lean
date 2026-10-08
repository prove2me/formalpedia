-- Prove2me | Theorems.Thm_FuzzyExtractors_LowerBound_lemma_C_1_large_T
-- name    : FuzzyExtractors.LowerBound.lemma_C_1_large_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:58.332019+00:00
-- url     : https://prove2.me/theorems/49c859a5-1888-4d7b-a091-48243e62a4a6
-- title:
--   Proof of Lemma C.1 — at least 2^{m′} points of S can produce the sketch value v
-- statement:
--   Let $\mathcal M$ be a finite set, $\mathsf{SS}$ a randomized sketching procedure on $\mathcal M$, and $S\subseteq\mathcal M$ nonempty. Let $W$ be uniform over $S$ and suppose $\tilde{\mathbf H}_\infty(W\mid\mathsf{SS}(W))\ge m'$. Then there is a sketch value $v$ such that the set
--   $$T = \{\,w\in S : \Pr[\mathsf{SS}(w)=v]>0\,\}$$
--   satisfies $|T|\ge 2^{m'}$.
--
--   This is the counting step of the proof of Lemma C.1: the points of $S$ consistent with an observed sketch value are numerous.
--
--   **Formalization Note** $m'$ is real and the comparison $2^{m'}\le|T|$ is made in the reals (no rounding of $2^{m'}$).
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix C, proof of Lemma C.1, p. 40, "there are at least 2^{m′} points w in S (call this set T) which could produce SS(W) = v"

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Appendix C, proof of Lemma C.1, p. 40: if `W` is uniform over a nonempty `S ⊆ 𝓜` and
`H̃∞(W | SS(W)) ≥ m'`, then for some sketch value `v` at least `2^m'` points `w ∈ S` can produce
the sketch value `v`. -/
theorem lemma_C_1_large_T {M V : Type} [Fintype M] (SS : M → PMF V) (S : Finset M)
    (hS : S.Nonempty) (m' : ℝ)
    (h : m' ≤ FuzzyExtractors.Hamming.avgMinEntropy (FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS))) :
    ∃ v : V, (2 : ℝ) ^ m' ≤ ((producers SS S v).card : ℝ) := by sorry

end FuzzyExtractors.LowerBound
