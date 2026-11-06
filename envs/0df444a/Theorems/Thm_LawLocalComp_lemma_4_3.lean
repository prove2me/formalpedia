-- Prove2me | Theorems.Thm_LawLocalComp_lemma_4_3
-- name    : LawLocalComp.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:09.16395+00:00
-- url     : https://prove2.me/theorems/70f2d794-9493-4275-a73a-7fe8eb27f0bc
-- title:
--   Lemma 4.3 (Merged value and moment cuts)
-- statement:
--   There is a family of law maps $\Phi_{N,Q,K,a}$ such that for integers $N\ge Q\ge2$, $K\ge8$, $1\le a\le K$, $\theta=1/K$ and every rational law $X$ of mean $\mu$, $Y=\Phi_{N,Q,K,a}(X)$ is a rational conditional-mean replacement with
--   $$0\le C_X(t)-C_Y(t)\le\theta\Big(\mathbb E[Y\mathbf 1\{Y>t\}]+\frac{\mu}{Q}+\frac tN\Big)\qquad(t\ge0),\tag{12}$$
--   and at most $V+H+4\sum_{u<R}m_u+2$ atoms, where
--   $$V=\Big\lceil\frac{\ln(NQ)}{\ln(1+1/a)}\Big\rceil,\quad H=\Big\lceil\frac{\ln(Q+1)}{\ln(1+a/K)}\Big\rceil,\quad R=\lceil\log_2K\rceil,\quad m_u=\big\lceil\sqrt{K2^{-u}}\big\rceil.$$
--   The maps are computable in time polynomial in the input bits, $K$, $\log N$ and $\log Q$. With Lemma 2.3 it gives the mixed-resource upper of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: bit cost polynomial in input and these parameters (N, Q, K, a) → one polynomial-time machine with N, Q, K, a in binary and a unary pad of length K; reason: polynomial in K and the bit lengths of N, Q is stronger than polynomial in N, Q, K, a; the cut counts V, H are polynomial in K and log(NQ)
--   - reading: (12) with no stated range of t → for t ≥ 0; reason: the range of (6), where the lemma is used
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 4.3, (12), p.7

import Mathlib
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_LawLocalComp_call
import Definitions.Def_LawLocalComp_upperMoment
import Definitions.Def_LawLocalComp_mean

namespace LawLocalComp

/-- **Lemma 4.3 (Merged value and moment cuts).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 4.3, (12), p.7.

There is one polynomial-time family of maps `Φ(N, Q, K, a)` such that for integers `N ≥ Q ≥ 2`,
`K ≥ 8`, `1 ≤ a ≤ K`, `θ = 1/K` and every rational law `X` of mean `µ`, `Y = Φ(N, Q, K, a)(X)` is a
rational conditional-mean replacement with
`0 ≤ C_X(t) − C_Y(t) ≤ θ(E[Y 1{Y > t}] + µ/Q + t/N)` for `t ≥ 0`, and at most
`V + H + 4∑_{u<R} m_u + 2` atoms, where `V = ⌈ln(NQ)/ln(1 + 1/a)⌉`, `H = ⌈ln(Q + 1)/ln(1 + a/K)⌉`,
`R = ⌈log₂ K⌉` and `m_u = ⌈√(K2^{−u})⌉`.

**Formalization Note.** "Bit cost is polynomial in input and these parameters" is `PolyLawMap` with
`N, Q, K, a` in binary and a unary pad of length `K` (so `a ≤ K` is covered; `N, Q` enter through
their bit lengths, which is stronger than polynomial in their values). -/
theorem lemma_4_3 : ∃ Φ : ℕ × ℕ × ℕ × ℕ → Law → Law,
    PolyLawMap (fun p => [(p.1 : ℚ), (p.2.1 : ℚ), (p.2.2.1 : ℚ), (p.2.2.2 : ℚ)]) (fun p => p.2.2.1)
      (fun _ => True) Φ ∧
    ∀ N Q K a : ℕ, Q ≤ N → 2 ≤ Q → 8 ≤ K → 1 ≤ a → a ≤ K → ∀ X : Law, IsRatLaw X →
      IsRatLaw (Φ (N, Q, K, a) X) ∧ IsCondMean X (Φ (N, Q, K, a) X) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ call X t - call (Φ (N, Q, K, a) X) t ∧
        call X t - call (Φ (N, Q, K, a) X) t ≤
          (1 / (K : ℝ)) * (upperMoment (Φ (N, Q, K, a) X) t + mean X / Q + t / N)) ∧
      (Φ (N, Q, K, a) X).w.support.card ≤
        ⌈Real.log (N * Q) / Real.log (1 + 1 / (a : ℝ))⌉₊ +
          ⌈Real.log (Q + 1) / Real.log (1 + (a : ℝ) / K)⌉₊ +
          4 * ∑ u ∈ Finset.range (Nat.clog 2 K), ⌈Real.sqrt (K * (2 : ℝ)⁻¹ ^ u)⌉₊ + 2 := by sorry

end LawLocalComp
