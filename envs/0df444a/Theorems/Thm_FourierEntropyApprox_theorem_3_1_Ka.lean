-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_1_Ka
-- name    : FourierEntropyApprox.theorem_3_1_Ka
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:21.431833+00:00
-- url     : https://prove2.me/theorems/fe6f62e4-fc13-4ddd-9812-daabca916d23
-- title:
--   Theorem 3.1, the constant: $K_a=\sum_{j\ge1}2^{-j}(j+3)^a=O(2^a a!)$
-- statement:
--   For every real $a\ge0$ the series
--
--   $$K_a=\sum_{j\ge1}2^{-j}(j+3)^a$$
--
--   converges, and there is an absolute constant $c>0$ such that for every real $a\ge0$
--
--   $$K_a\le c\,2^a\,\Gamma(a+1),$$
--
--   i.e. $K_a=O(2^a a!)$, with $a!=\Gamma(a+1)$.
--
--   The bound makes the constant of Theorem 3.1 explicit in the growth exponent $a$; Theorem 3.2 uses $a=1$.
--
--   **Formalization Note** The series is `Ka a`, a `tsum` over $j\ge1$; the first clause states that it converges, so the `tsum` is the page's sum.
--
--   Differences from the source:
--   - reading: $a!$ for real $a\ge0$, and $O(\cdot)$ → $\Gamma(a+1)$, with one constant $c$ for all $a\ge0$; reason: $a$ is real in Theorem 3.1, $\Gamma(a+1)=a!$ at integers, and an $O$ in $a$ is uniform in $a$
--   - encoding: the equation $K_a=\sum_{j\ge1}\dots$ → an explicit convergence clause for every $a\ge0$; reason: the page treats $K_a$ as a finite number; a Lean `tsum` needs the convergence stated
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 3.1, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_FourierEntropyApprox_Ka

namespace FourierEntropyApprox

/-- **Theorem 3.1, the constant `K_a`.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.14:
"where K_a = ∑_{j≥1} 2^{−j}(j + 3)^a = O(2^a a!)."

For every `a ≥ 0` the series `∑_{j≥1} 2^{−j}(j + 3)^a` converges, and there is an absolute `c > 0` with
`K_a ≤ c · 2^a · Γ(a + 1)` for every real `a ≥ 0`.

**Formalization Note.** `a` is real (`a ≥ 0` in Theorem 3.1), so `a!` is read as `Γ(a + 1)`, which agrees
with `a!` at integers. The `O(·)` is uniform in `a ≥ 0`. The series is indexed by `j + 1` with `j : ℕ`. -/
theorem theorem_3_1_Ka :
    (∀ a : ℝ, 0 ≤ a → Summable (fun j : ℕ => KaTerm a (j + 1))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 ≤ a → Ka a ≤ c * (2 : ℝ) ^ a * Real.Gamma (a + 1) := by sorry

end FourierEntropyApprox
