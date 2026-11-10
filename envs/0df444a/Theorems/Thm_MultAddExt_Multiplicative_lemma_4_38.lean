-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_4_38
-- name    : MultAddExt.Multiplicative.lemma_4_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:46:36.059783+00:00
-- url     : https://prove2.me/theorems/bbc64fe1-45d4-49b6-811d-3d69ce1b9435
-- title:
--   Lemma 4.38 — Johnson bound for list recovery: at most 2K/ξ² polynomials
-- statement:
--   Let $\mathbb F_q$ be a finite field, $\hat h, K\ge 0$ integers, and $S_t\subseteq\mathbb F_q$ with $|S_t|\le K$ for every $t\in\mathbb F_q$. Let $\xi>0$ with $q\xi^2\ge 2\hat hK$. Then the number of polynomials $p\in\mathbb F_q[t]$ of degree at most $\hat h$ such that $p(t)\in S_t$ for at least a $\xi$ fraction of the field elements $t$ is at most
--   $$\frac{2K}{\xi^2}.$$
--
--   It bounds the list of candidate polynomials that the reconstruction step has to pin down.
--
--   Differences from the source:
--   - encoding: a ξ fraction, with the bound 2K/ξ² → hypothesis 0 < ξ; reason: the bound 2K/ξ² is undefined at ξ = 0 (Lean would read it as 0, which the count of constant polynomials exceeds when ĥK = 0); the hypothesis excludes only the undefined case
--   - encoding: the number of degree-at-most-ĥ polynomials with p(t) ∈ S_t on at least ξq points → Set.ncard of {p : natDegree p ≤ ĥ ∧ ξ·q ≤ #{t : p(t) ∈ S_t}}; reason: the set is finite (polynomials of degree ≤ ĥ over a finite field), so ncard is its cardinality; natDegree ≤ ĥ includes the zero polynomial, as deg 0 = −∞ ≤ ĥ
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 26 (PDF 30), Lemma 4.38

import Mathlib

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 4.38** (Johnson bound for list recovery), p. 26. Suppose `S_t ⊆ F_q` and `|S_t| ≤ K`
for every `t`. If `qξ² ≥ 2ĥK`, the number of polynomials of degree at most `ĥ` satisfying
`p(t) ∈ S_t` on at least a `ξ` fraction of the field elements `t ∈ F_q` is at most `2K/ξ²`. -/
theorem lemma_4_38 {F : Type*} [Fintype F] [Field F] [DecidableEq F] (S : F → Finset F)
    (K h : ℕ) (hS : ∀ t, (S t).card ≤ K) (ξ : ℝ) (hξ : 0 < ξ)
    (hq : 2 * (h : ℝ) * K ≤ (Fintype.card F : ℝ) * ξ ^ 2) :
    ({p : Polynomial F | p.natDegree ≤ h ∧
        ξ * (Fintype.card F : ℝ) ≤ ((Finset.univ.filter (fun t => p.eval t ∈ S t)).card : ℝ)}.ncard
      : ℝ) ≤ 2 * K / ξ ^ 2 := by sorry

end MultAddExt.Multiplicative
