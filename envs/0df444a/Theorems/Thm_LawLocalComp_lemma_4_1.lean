-- Prove2me | Theorems.Thm_LawLocalComp_lemma_4_1
-- name    : LawLocalComp.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:23.408144+00:00
-- url     : https://prove2.me/theorems/2f187716-e1d6-42aa-9962-f77c8bd18856
-- title:
--   Lemma 4.1 (Horizon cells)
-- statement:
--   There is a family of law maps $\Phi_{k,N}$, computable in time polynomial in the input bits, $k$ and $\log N$, such that for integers $N,k\ge2$ and every rational law $X$ of mean $\mu$, $Y=\Phi_{k,N}(X)$ is a rational conditional-mean replacement of $X$ with
--   $$C_X(t)-C_Y(t)\le k^{-2}\,\mathbb E[Y\mathbf 1\{Y>t\}]+\frac{\mu+t}{Nk^2}\qquad(t\ge0),$$
--   and at most
--   $$2k\lceil\log_2N\rceil+\Big\lceil\frac{\ln(N+1)}{\ln(1+1/k)}\Big\rceil+24k\tag{10}$$
--   atoms. With Lemma 2.3 it gives the horizon upper of Theorem 1.1.
--
--   **Formalization Note** The machine reads $N$ in binary and a unary pad of length $k$.
--
--   Differences from the source:
--   - reading: polynomial bit cost in input, k, log N → PolyLawMap: one polynomial-time machine with N in binary and a unary pad of length k; reason: the literal reading of polynomial in k and log N
--   - reading: at most (10) cells → at most (10) output atoms; reason: each cell carries one atom (coincident means merge)
--   - reading: call certificate with no stated range of t → the certificate for t ≥ 0; reason: the range of (6), where the lemma is used; at very negative t the right side is negative
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 4.1, (10), p.6

import Mathlib
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_LawLocalComp_call
import Definitions.Def_LawLocalComp_upperMoment
import Definitions.Def_LawLocalComp_mean

namespace LawLocalComp

/-- **Lemma 4.1 (Horizon cells).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 4.1, (10), p.6.

There is one polynomial-time family of maps `Φ(k, N)` such that for integers `N, k ≥ 2` and every
rational law `X` of mean `µ`, `Y = Φ(k, N)(X)` is a rational conditional-mean replacement with
`C_X(t) − C_Y(t) ≤ k^{−2}E[Y 1{Y > t}] + (µ + t)/(Nk²)` for `t ≥ 0` and at most
`2k⌈log₂ N⌉ + ⌈ln(N + 1)/ln(1 + 1/k)⌉ + 24k` atoms.

**Formalization Note.** "Polynomial bit cost in input, k, log N" is `PolyLawMap` with `N` in binary
and a unary pad of length `k`. The number of output atoms is bounded by the number of cells. -/
theorem lemma_4_1 : ∃ Φ : ℕ × ℕ → Law → Law,
    PolyLawMap (fun p => [(p.1 : ℚ), (p.2 : ℚ)]) (fun p => p.1) (fun _ => True) Φ ∧
    ∀ N k : ℕ, 2 ≤ N → 2 ≤ k → ∀ X : Law, IsRatLaw X →
      IsRatLaw (Φ (k, N) X) ∧ IsCondMean X (Φ (k, N) X) ∧
      (∀ t : ℝ, 0 ≤ t → call X t - call (Φ (k, N) X) t ≤
        upperMoment (Φ (k, N) X) t / (k : ℝ) ^ 2 + (mean X + t) / (N * (k : ℝ) ^ 2)) ∧
      ((Φ (k, N) X).w.support.card : ℝ) ≤
        2 * k * Nat.clog 2 N + ⌈Real.log (N + 1) / Real.log (1 + 1 / (k : ℝ))⌉₊ + 24 * k := by sorry

end LawLocalComp
