-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_3_2
-- name    : OptQJunta.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:15:23.88589+00:00
-- url     : https://prove2.me/theorems/d2969cef-13bd-48e6-b285-2c8edc230ea8
-- title:
--   Theorem 3.2 — union size testing from $O(k/(\delta\log(ek)))$ independent samples
-- statement:
--   Fix a finite set $\Omega$, an integer $k\ge1$ and $0<\delta\le1$. Given independent samples from a distribution $\mathcal D$ on $2^\Omega$, there is a randomized algorithm for Problem 3.1 that succeeds with probability at least $2/3$ and uses
--
--   $$
--   O\Big(\frac{k}{\delta\log(ek)}\Big)
--   $$
--
--   samples, $\log$ the base-two logarithm. Here Problem 3.1 asks to distinguish YES (some $T\subseteq\Omega$ with $|T|\le k$ has $\Pr_{X\sim\mathcal D}[X\subseteq T]=1$) from NO (every $T$ with $|T|\le k$ has $\Pr[X\not\subseteq T]\ge\delta$).
--
--   The bound is independent of $|\Omega|$, and it is optimal by Theorem 3.14. Through influence sampling it yields the forward-only and channel upper bounds, Theorems 5.5 and 6.2.
--
--   **Formalization Note** The implicit constant $C$ is absolute and quantified before $\Omega$, $k$, $\delta$. The algorithm is an acceptance rule $F$ on $t$ samples (§2.5.4) depending on $\Omega,k,\delta$ only; it must accept with probability at least $2/3$ on YES and at most $1/3$ on NO.
--
--   Differences from the source:
--   - encoding: O(·) bound on the number of queries/samples → ∃ C > 0, fixed before every parameter, with count ≤ C·(bound); reason: the paper's O(·) has an absolute implicit constant (§2.1 conventions, as in the published Theorems 3.19 and 4.2)
--   - encoding: a randomized algorithm (tester) using t independent samples → an acceptance rule F : 𝒳^t → [0, 1], independent of the distribution, with acceptance probability E_{Y∼p^{⊗t}}[F(Y)] (sampleAcc); reason: §2.5.4 (p.23) shows every tester requesting at most t samples, adaptively and with private randomness, has exactly this form; a tester using fewer samples ignores the rest
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 3.2, p.26 (Problem 3.1, p.26; §2.5.4, p.23)

import Mathlib
import Definitions.Def_OptQJunta_Supplement_sampleAcc

namespace OptQJunta.Supplement

/-- **Theorem 3.2** (Upper bound for Union Size Testing from independent samples; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.26).
Fix a finite set `Ω`, an integer `k ≥ 1`, and `0 < δ ≤ 1`. Given independent samples from a
distribution `𝒟` on `2^Ω`, there is a randomized algorithm for Problem 3.1 that succeeds with
probability at least `2/3` and uses `O(k/(δ log(ek)))` samples.

**Formalization Note** `O` is an absolute constant `C > 0` fixed before `Ω`, `k`, `δ`; `log` is base
`2` (§2.1, p.12) and `e = exp 1`. The algorithm is a `t`-sample acceptance rule `F` into `[0, 1]`
(§2.5.4, p.23), chosen knowing `Ω`, `k`, `δ` but not `𝒟`; it accepts (YES) with probability
`≥ 2/3` on every YES distribution and `≤ 1/3` on every NO distribution. -/
theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ), 1 ≤ k →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ (t : ℕ) (F : (Fin t → Finset Ω) → ℝ),
          (t : ℝ) ≤ C * k / (δ * Real.logb 2 (Real.exp 1 * k)) ∧ IsTestFn F ∧
          ∀ D : Finset Ω → ℝ, IsDist D →
            (UnionYesOn D k → 2 / 3 ≤ sampleAcc F D) ∧
              (UnionNoOn D k δ → sampleAcc F D ≤ 1 / 3) := by sorry

end OptQJunta.Supplement
