-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_8
-- name    : MomentSearch.Supplement.theorem_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T09:33:46.452204+00:00
-- url     : https://prove2.me/theorems/88c0434b-ebb1-4467-8601-0167e9098b93
-- title:
--   Theorem 8 — quantile sketches: $d_K(p,\pi)\le 1/q$, and $\lceil n^{\varepsilon}\rceil$ quantiles give an $O(1/\varepsilon)$-approximation with $O(n^{\varepsilon}\log n)$ bits
-- statement:
--   Let $n\ge2$.
--
--   1. For every integer $q\ge1$ and every $p\in\Delta_n$, let $x_1,\dots,x_q$ be the $q$-quantiles of $p$ and let $\pi$ place mass $1/q$ at each $x_\ell$ (adding masses when quantiles repeat). Then $\pi\in\Delta_n$ and
--   $$d_K(p,\pi)\le\frac1q .$$
--   2. There are absolute constants $C_1,C_2>0$ such that for every $\varepsilon\in(0,1)$ and $q=\lceil n^{\varepsilon}\rceil$: the $q$-quantile sketch takes finitely many values on $\Delta_n$, at most $2^b$ of them for some integer $b\le C_1 n^{\varepsilon}\log_2 n$ (a sketch of $O(n^\varepsilon\log n)$ bits); and for every $p\in\Delta_n$, Coarse Greedy with parameter $\varepsilon$ and nominal distribution $\pi$ built from the quantiles of $p$ (for any choice of $\pi$-medians) satisfies
--   $$\mathrm{cost}_p(\text{Coarse Greedy})\le\frac{C_2}{\varepsilon}\,\mathrm{OPT}(p).$$
--
--   This shows that the information-theoretic lower bound of Theorem 6 is tight up to constant factors, both in the number of bits and in the approximation ratio.
--
--   Differences from the source:
--   - encoding: the q-quantiles of p suffice to construct a distribution π → π := quantileDist n q (quantileSketch n q p), a function of the quantile tuple alone; reason: this is the paper's construction (mass 1/q at each quantile, p.9 and p.18)
--   - reading: a sketch of O(n^ε log n) bits → the image of the quantile sketch on Δ_n is finite with at most 2^b elements, for an integer b ≤ C₁ n^ε log₂ n, C₁ absolute; reason: §3.1 (p.7): encodable with b bits means |σ(Δ_n)| ≤ 2^b
--   - reading: guarantees an O(1/ε)-approximation via Coarse Greedy → ∃ C₂ > 0 absolute: for every p ∈ Δ_n and every median rule, cost_p of Coarse Greedy with parameter ε and nominal π(quantiles of p) is ≤ (C₂/ε)·OPT(p); reason: the proof (p.18) applies Theorem 5 to the ball of radius n^{−ε} around π; Coarse Greedy fixes no median, so every rule is covered
--   - encoding: distribution p on [n]₀ (part 1) → n ≥ 2 as a hypothesis; reason: the paper's standing assumption n ≥ 2 (§2.1)
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 8, p.9 (PDF p.11); restated with proof App. B.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MomentSearch_OPT
import Definitions.Def_MomentSearch_Supplement_cdf
import Definitions.Def_MomentSearch_Supplement_coarseGreedy
import Definitions.Def_MomentSearch_Supplement_quantileDist

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 8** (Quantile upper bound) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 8, p.9 (PDF p.11); restated with proof
App. B.2, p.18 (PDF p.20)).

1. For every `n ≥ 2`, every integer `q ≥ 1` and every `p ∈ Δ_n`, the distribution `π`
   placing mass `1/q` at each `q`-quantile of `p` (adding masses when quantiles repeat) lies
   in `Δ_n` and satisfies `d_K(p, π) ≤ 1/q`; `π` is computed from the quantiles alone.
2. There are absolute constants `C₁, C₂ > 0` such that for `n ≥ 2`, `ε ∈ (0, 1)` and
   `q = ⌈n^ε⌉`: the `q`-quantile sketch takes at most `2^b` values on `Δ_n` for some integer
   `b ≤ C₁ n^ε log₂ n` (a sketch of `O(n^ε log n)` bits), and for every `p ∈ Δ_n` Coarse Greedy
   with parameter `ε` and nominal distribution `π` (any choice of `π`-medians) satisfies
   `cost_p ≤ (C₂/ε)·OPT(p)` (an `O(1/ε)`-approximation).

**Formalization Note.** `O(·)` are absolute constants chosen before `n`, `ε`, `p`. The
`q`-quantiles are `x_ℓ = min{t ∈ [n]₀ : P(t) ≥ ℓ/q}`, `ℓ = 1, …, q`. `log` is base 2. -/
theorem theorem_8 :
    (∀ (n : ℕ), 2 ≤ n → ∀ q : ℕ, 1 ≤ q → ∀ p ∈ stdSimplex ℝ (Fin n),
        quantileDist n q (quantileSketch n q p) ∈ stdSimplex ℝ (Fin n) ∧
          kolDist p (quantileDist n q (quantileSketch n q p)) ≤ 1 / q) ∧
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ '' stdSimplex ℝ (Fin n)).Finite ∧
        (∃ b : ℕ, (b : ℝ) ≤ C₁ * (n : ℝ) ^ ε * Real.logb 2 n ∧
          (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ '' stdSimplex ℝ (Fin n)).ncard ≤ 2 ^ b) ∧
        ∀ p ∈ stdSimplex ℝ (Fin n), ∀ med : ℕ → ℕ → ℕ,
          IsMedianRule (quantileDist n ⌈(n : ℝ) ^ ε⌉₊ (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ p)) med →
          cost p (coarseGreedy
              (quantileDist n ⌈(n : ℝ) ^ ε⌉₊ (quantileSketch n ⌈(n : ℝ) ^ ε⌉₊ p)) ε med) ≤
            C₂ / ε * OPT p := by sorry

end MomentSearch.Supplement
