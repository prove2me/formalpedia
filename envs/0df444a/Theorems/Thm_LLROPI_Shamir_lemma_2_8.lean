-- Prove2me | Theorems.Thm_LLROPI_Shamir_lemma_2_8
-- name    : LLROPI.Shamir.lemma_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:33:19.13311+00:00
-- url     : https://prove2.me/theorems/3c728e1a-668d-43d9-a61b-b821b9cfb030
-- title:
--   Lemma 2.8 (U³-gap) — a nearly $\pm1$-valued $f$ with $|\mathbb Ef|\le1-2\tau+o(1)$ has $\|f\|_{U^3}\le q<1$
-- statement:
--   For every fixed $\tau\in(0,1/2)$ there is $q<1$ such that the following holds for all sufficiently large primes $p$. If $f:\mathbb F_p\to\mathbb R$ satisfies $\big||f(x)|-1\big|=o(1)$ uniformly over $x\in\mathbb F_p$, and $\big|\mathbb E_{x\in\mathbb F_p}f(x)\big|\le1-2\tau+o(1)$, then $\|f\|_{U^3}\le q$.
--
--   Formally: $q<1$ is chosen first, then a slack $\eta>0$ and a threshold $P_0$; for every prime $p\ge P_0$ and every $f$ with $\big||f(x)|-1\big|\le\eta$ for all $x$ and $|\mathbb Ef|\le1-2\tau+\eta$, the Gowers $U^3$ norm (Definition 2.7) satisfies $\|f\|_{U^3}\le q$.
--
--   Differences from the source:
--   - reading: o(1) errors, for all sufficiently large primes p → a slack η > 0 and a threshold P₀ chosen after q; reason: equivalent to the sequential form: if it failed for every η, P₀, a sequence of counterexamples with errors → 0 would violate the sequential statement
--   - encoding: ‖f‖_{U³} of a real function f → ShamirLeak.gowersNorm 3 of the complex coercion of f; reason: Definition 2.7 applies to complex functions; the published definition matches it
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.8, p. 22 (PDF 24)

import Mathlib
import Definitions.Def_ShamirLeak_gowersNorm

namespace LLROPI.Shamir

/-- **Lemma 2.8 (U³-gap)**, p. 22 (PDF 24). For every fixed `τ ∈ (0, 1/2)` there is `q < 1` such
that for all sufficiently large primes `p`: if `f : 𝔽_p → ℝ` satisfies `||f(x)| − 1| = o(1)`
uniformly over `x ∈ 𝔽_p` and `|E_{x ∈ 𝔽_p} f(x)| ≤ 1 − 2τ + o(1)`, then `‖f‖_{U³} ≤ q`.
Sun, Wootters, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.8, p. 22 (PDF 24).

**Formalization Note.** The `o(1)` errors (as `p → ∞`, uniform in `x`) are read as one slack
`η > 0` with a threshold `P₀`, both chosen after `q`: this is equivalent to the sequential form.
The Gowers norm is the published `ShamirLeak.gowersNorm 3` (Definition 2.7). -/
theorem lemma_2_8 (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) :
    ∃ q : ℝ, q < 1 ∧ ∃ η : ℝ, 0 < η ∧ ∃ P₀ : ℕ,
      ∀ (p : ℕ) [Fact p.Prime], P₀ ≤ p → ∀ f : ZMod p → ℝ,
        (∀ x, |(|f x| - 1)| ≤ η) →
        |(∑ x, f x) / (p : ℝ)| ≤ 1 - 2 * τ + η →
          ShamirLeak.gowersNorm 3 (fun x => (f x : ℂ)) ≤ q := by sorry

end LLROPI.Shamir
