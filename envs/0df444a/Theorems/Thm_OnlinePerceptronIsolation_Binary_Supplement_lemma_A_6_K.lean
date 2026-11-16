-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_Supplement_lemma_A_6_K
-- name    : OnlinePerceptronIsolation.Binary.Supplement.lemma_A_6_K
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:58.687205+00:00
-- url     : https://prove2.me/theorems/4d1e417c-1a71-483f-b071-4f0e845f00ee
-- title:
--   Lemma A.6 (ONLINE_K version, §4.3) — averaging over independent seeds
-- statement:
--   Fix dimensions $m,n$, a set $K\subseteq\mathbb R$, a real radius $h$ and a real bound $b_n$. Suppose every deterministic online algorithm $A^*$ satisfies
--   $$\mathbb P_G\{A^*(G)\in S^h(G,K)\}\le b_n.$$
--   Then every jointly measurable randomized online algorithm $A$, with any independent probability seed law $\nu$, satisfies
--   $$\mathbb P_{\xi,G}\{A(\xi,G)\in S^h(G,K)\}\le b_n.$$
--   The bound has no added slack and imposes no well-separation condition on $K$. This is the randomization reduction invoked in Theorem 3.2. Dimensions and the radius remain fixed during the averaging.
--
--   Differences from the source:
--   - encoding: one-based sign cube and real coordinates → zero-based Fin indices and exact real-valued signs; reason: coordinate relabelling preserves all signings, scores and Hamming distances
--   - encoding: probability over Gaussian inputs and internal randomness → the real value of the product Gaussian measure and arbitrary independent seed laws with jointly measurable online sections; reason: this represents the full randomized class; measure values also give outer probabilities for arbitrary K in the unrestricted supporting lemmas
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma A.6 (ONLINE_K version, §4.3), printed p. 15, PDF p. 17; original Lemma A.6 and Eqs. (A.60)–(A.61), printed p. 24, PDF p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RandomSuccessK
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

universe u
/-- Section 4.3 applies the averaging lemma verbatim to ONLINE_K, with no slack. -/
theorem lemma_A_6_K (m n : ℕ) (K : Set ℝ) (h bₙ : ℝ)
    (hbound : ∀ A : Fin n → (Fin m × Fin n → ℝ) → ℝ,
      ABPOnline.IsOnlineAlg m n A → detSuccessK A K h ≤ bₙ) :
    ∀ {Ξ : Type u} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
      (A : Ξ → Fin n → (Fin m × Fin n → ℝ) → ℝ),
      IsRandomizedOnline A → randomSuccessK ν A K h ≤ bₙ := by sorry

end OnlinePerceptronIsolation.Binary.Supplement
