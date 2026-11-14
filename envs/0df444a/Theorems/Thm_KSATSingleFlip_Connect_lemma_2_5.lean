-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_5
-- name    : KSATSingleFlip.Connect.lemma_2_5
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:19:48.081658+00:00
-- url     : https://prove2.me/theorems/f83fae95-5d69-4dfc-b4f0-96a61b832c94
-- title:
--   Lemma 2.5 — Sampling without replacement
-- statement:
--   Title: Lemma 2.5 — Sampling without replacement
--
--   Let 0 ≤ d ≤ N and let a₁, …, a_N be nonnegative real numbers. If I is a uniformly chosen d-element subset of {1, …, N}, then
--
--   $$\mathbb E\!\left[\prod_{i\in I} a_i\right] \le \left(\frac1N\sum_{i=1}^N a_i\right)^d.$$
--
--   The formal statement includes the empty case N = d = 0 using the usual empty-product and zeroth-power conventions. This is an open target.
--
--   Source: Chunyang Wang, Yitong Yin, Yixiao Yu, and Yiyao Zhang, *Single-Variable Connectivity in Random k-SAT*, Lemma 2.5, printed p. 12 (PDF p. 14 of STOC 2027 submission #737), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, Lemma 2.5, printed p. 12 (PDF p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Lemma 2.5: the expected product from sampling without replacement is
at most the corresponding power of the arithmetic mean. -/
theorem lemma_2_5 (N d : ℕ) (hd : d ≤ N) (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) :
    uexp (fun I : {I : Finset (Fin N) // I.card = d} => ∏ i ∈ I.1, a i) ≤ (uexp a) ^ d := by
  sorry

end KSATSingleFlip.Connect
