-- Prove2me | Theorems.Thm_FuzzyExtractors_LowerBound_lemma_C_1_good_value
-- name    : FuzzyExtractors.LowerBound.lemma_C_1_good_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:33.611824+00:00
-- url     : https://prove2.me/theorems/31271ead-6d77-45eb-9723-1701746bb68f
-- title:
--   Proof of Lemma C.1 — some sketch value v leaves H∞(W | SS(W) = v) ≥ m′
-- statement:
--   Let $\mathcal M$ be a finite set, $\mathsf{SS}$ a randomized sketching procedure on $\mathcal M$, and $S\subseteq\mathcal M$ nonempty. Let $W$ be uniform over $S$ and suppose $\tilde{\mathbf H}_\infty(W\mid\mathsf{SS}(W))\ge m'$. Then there is a sketch value $v$ with $\Pr[\mathsf{SS}(W)=v]>0$ such that for every $w$,
--   $$\Pr[W=w \wedge \mathsf{SS}(W)=v] \le 2^{-m'}\,\Pr[\mathsf{SS}(W)=v],$$
--   that is, $\mathbf H_\infty(W\mid \mathsf{SS}(W)=v)\ge m'$.
--
--   This is the first step of the proof of Lemma C.1: an average bound on the guessing probability yields one value of the sketch where the bound holds.
--
--   **Formalization Note** The conditional min-entropy is written in joint form, multiplied through by $\Pr[\mathsf{SS}(W)=v]$, so no division by a probability occurs; positivity of $\Pr[\mathsf{SS}(W)=v]$ is part of the conclusion. Probabilities are in $[0,\infty]$ (`ENNReal`), and $2^{-m'}$ is embedded from the reals.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors, arXiv:cs/0602007v4, Appendix C, proof of Lemma C.1, p. 40, "In particular, there must be some value v such that H∞(W | SS(W) = v) ≥ m′"

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

namespace FuzzyExtractors.LowerBound

/-- Appendix C, proof of Lemma C.1, p. 40: if `W` is uniform over a nonempty `S ⊆ 𝓜` and
`H̃∞(W | SS(W)) ≥ m'`, then some sketch value `v` has positive probability and
`H∞(W | SS(W) = v) ≥ m'`, i.e. `Pr[W = w ∧ SS(W) = v] ≤ 2^(-m') · Pr[SS(W) = v]` for every `w`. -/
theorem lemma_C_1_good_value {M V : Type} [Fintype M] (SS : M → PMF V) (S : Finset M)
    (hS : S.Nonempty) (m' : ℝ)
    (h : m' ≤ FuzzyExtractors.Hamming.avgMinEntropy (FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS))) :
    ∃ v : V, 0 < ((PMF.uniformOfFinset S hS).bind SS) v ∧
      ∀ w : M, FuzzyExtractors.Hamming.withSketch SS (PMF.uniformOfFinset S hS) (w, v) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-m')) * ((PMF.uniformOfFinset S hS).bind SS) v := by sorry

end FuzzyExtractors.LowerBound
