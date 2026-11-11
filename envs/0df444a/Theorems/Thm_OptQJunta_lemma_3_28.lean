-- Prove2me | Theorems.Thm_OptQJunta_lemma_3_28
-- name    : OptQJunta.lemma_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:20:32.729992+00:00
-- url     : https://prove2.me/theorems/8444d7e9-29db-4604-9d1e-216edf35b5de
-- title:
--   Lemma 3.28 — finite moment-matched priors with $\mu_0((0,\infty))\le D^2a/(b-a)$
-- statement:
--   For $0<a<b$ and an integer $D\ge1$, there are finitely supported probability measures $\mu_0,\mu_1$ on $\{0\}\cup[a,b]$ whose moments agree through degree $D$, with $\mathrm{supp}(\mu_1)\subseteq[a,b]$ and
--
--   $$
--   \mu_0\bigl((0,\infty)\bigr)\le\frac{D^2a}{b-a}.
--   $$
--
--   Encoded in parity-address functions, these priors give the lower bound of Lemma 4.9.
--
--   **Formalization Note** A finitely supported probability measure is a finite set of atoms with nonnegative weights summing to $1$; the moments of degree $0,\dots,D$ agree.
--
--   Differences from the source:
--   - encoding: finitely supported probability measures on $\mathbb R$ → finite sets of atoms with nonnegative weights summing to $1$; reason: a finitely supported probability measure is exactly such a weighted finite set
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 3.28, p.53

import Mathlib

namespace OptQJunta

/-- **Lemma 3.28** (Finite moment-matched priors; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.53). For `0 < a < b` and integer `D ≥ 1`,
there are finitely supported probability measures `μ0, μ1` on `{0} ∪ [a, b]` whose moments agree
through degree `D`, with `supp(μ1) ⊆ [a, b]` and `μ0((0, ∞)) ≤ D²a/(b − a)`.

**Formalization Note** A finitely supported probability measure is a finite set of atoms `s` with
nonnegative weights `w` summing to `1`. "Moments agree through degree `D`" is
`Σ w₀(x) x^d = Σ w₁(x) x^d` for `0 ≤ d ≤ D`, and `μ0((0, ∞))` is the weight on positive atoms. -/
theorem lemma_3_28 (a b : ℝ) (ha : 0 < a) (hab : a < b) (D : ℕ) (hD : 1 ≤ D) :
    ∃ (s0 s1 : Finset ℝ) (w0 w1 : ℝ → ℝ),
      (∀ x ∈ s0, 0 ≤ w0 x) ∧ (∀ x ∈ s1, 0 ≤ w1 x) ∧
      ∑ x ∈ s0, w0 x = 1 ∧ ∑ x ∈ s1, w1 x = 1 ∧
      (∀ x ∈ s0, x = 0 ∨ x ∈ Set.Icc a b) ∧ (∀ x ∈ s1, x ∈ Set.Icc a b) ∧
      (∀ d : ℕ, d ≤ D → ∑ x ∈ s0, w0 x * x ^ d = ∑ x ∈ s1, w1 x * x ^ d) ∧
      ∑ x ∈ s0.filter (fun x => 0 < x), w0 x ≤ (D : ℝ) ^ 2 * a / (b - a) := by sorry

end OptQJunta
