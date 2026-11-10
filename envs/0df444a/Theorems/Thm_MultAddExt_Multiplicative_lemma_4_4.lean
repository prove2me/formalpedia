-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_4_4
-- name    : MultAddExt.Multiplicative.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:22.430194+00:00
-- url     : https://prove2.me/theorems/9114c5bb-8ba8-46ae-b7d1-815f2204df97
-- title:
--   Lemma 4.4 — conditioning on an event of probability p costs at most log(1/p) bits of min-entropy
-- statement:
--   Let $Y$ be a random variable on a finite set, defined on a finite probability space together with an event $E$ of probability $p=\Pr[E]>0$. If $H_\infty(Y)\ge k$, then
--   $$H_\infty(Y\mid E)\ \ge\ k-\log(1/p),$$
--   where $H_\infty(Y\mid E)$ is the min-entropy of the conditional distribution of $Y$ given $E$ and $\log$ is base $2$.
--
--   The lemma is used throughout the paper whenever a source is conditioned on the value of a seed or on a postselection event.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: an event E jointly defined with Y → Y : Ω → β a function of an outcome ω of a distribution P on a finite set Ω, and E ⊆ Ω; reason: every pair of a random variable and an event on a finite space is of this form
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 19 (PDF 23), Lemma 4.4

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 4.4** (Conditioning on an event), p. 19. If `H∞(Y) ≥ k` and `E` is an event jointly
defined with `Y` of probability `p > 0`, then `H∞(Y | E) ≥ k − log(1/p)`. Here `Y` is a function of
an outcome `ω` drawn from the distribution `P` on a finite set `Ω`, and `E ⊆ Ω`. -/
theorem lemma_4_4 {Ω β : Type*} [Fintype Ω] [Fintype β] [Nonempty β] (P : Ω → ℝ)
    (hP : IsDist P) (Y : Ω → β) (E : Set Ω) (k : ℝ) (hp : 0 < probEvent P E)
    (hk : k ≤ minEntropy (pushforward Y P)) :
    k - Real.logb 2 (1 / probEvent P E) ≤ minEntropy (pushforward Y (condDist P E)) := by sorry

end MultAddExt.Multiplicative
