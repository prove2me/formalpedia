-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_1_1
-- name    : GaussDiffSVP.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:49:10.66105+00:00
-- url     : https://prove2.me/theorems/3a00c40f-3b0c-46ba-b0d3-535b74f82066
-- title:
--   Theorem 1.1 — single sample DGS above smoothing in time $2^{\alpha_G n+o(n)}$, space $2^{\beta_G n+o(n)}$
-- statement:
--   Write $\alpha_G=\tfrac12\log_2(3/2)$ and $\beta_G=\tfrac12\log_2(4/3)$. Fix $\alpha>1$ and $\xi>0$. There is a classical randomized algorithm that, given a full rank rational lattice $L=B\mathbb Z^n$, a rational shift $a$ and a positive rational squared width $\sigma^2$ with
--   $$\sigma\ge\alpha\,\eta_{1/2}(L),$$
--   outputs a point $X\in a+L$ with
--   $$d_{TV}\big(\mathcal L(X),D_{a+L,\sigma}\big)\le\exp\!\big[-\Omega\big(n/\log^{2+\xi}(n+2)\big)\big],$$
--   in time $2^{\alpha_G n+o(n)}$ and bit space $2^{\beta_G n+o(n)}$, on every execution.
--
--   The constants may depend on $\alpha$ and $\xi$. This is the paper's Gaussian sampler at the BDGL time and space exponents; it is the single-sample application of the counting-moment framework.
--
--   **Formalization Note** One program, one $g$ with $g(n)/n\to0$, one exponent $K$ and one $c>0$ are fixed after $\alpha,\xi$; the bounds hold for every $n\ge1$ and every input with the factor $(\ell+1)^K$, and the error is $\exp(-cn/\log^{2+\xi}(n+2))$ with the natural logarithm.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - encoding: o(n), exp[−Ω(·)], suppressed polynomial factors in the input length → one g with g(n)/n → 0, exp(−c·(·)) with one c > 0 for every n ≥ 1, a factor (ℓ+1)^K; program, g, K, c fixed after the fixed parameters and before n and the input; reason: reading of the asymptotic notation as in the published goal; App. C.1.4 (p.81) covers the finitely many small ranks
--   - encoding: output points X ∈ a + L and their law → rational coordinate words, every output on every coin tape a tuple of points of a + L, total variation ½Σ over output words; reason: points of a + L are rational and the word encoding is injective, so the laws correspond
--   - encoding: η_ε(L) defined by ρ_{1/η}(L*∖{0}) = ε → the published smoothingParam, the infimum of s > 0 with ρ_{1/s}(L*∖{0}) ≤ ε; reason: the dual mass is continuous and strictly decreasing in s, so both give the same value
--   - encoding: a full rank rational lattice L = Bℤⁿ → a nonsingular B ∈ ℚ^{n×n}, n ≥ 1; reason: same instances; the rank-0 lattice is excluded as in the published goal
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 1.1, p.6 (proved in §7)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_DGS

open Filter Topology TwMSOCount.Main CosetTreeSVP.SVP

namespace GaussDiffSVP.Supplement

/-- Theorem 1.1 (Single sample DGS above smoothing) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.6). Fix `α > 1` and `ξ > 0`. There
is a classical randomized algorithm that, given a full rank rational lattice `L`, a rational shift
`a`, and a positive rational squared width `σ²` with `σ ≥ αη_{1/2}(L)`, outputs `X ∈ a + L` with
`d_TV(L(X), D_{a+L,σ}) ≤ exp[−Ω(n / log^{2+ξ}(n + 2))]`. Its time is `2^{α_G n + o(n)}` and its bit
space is `2^{β_G n + o(n)}`, with `α_G = ½ log₂(3/2)`, `β_G = ½ log₂(4/3)`.

Formally: for fixed `α, ξ` there are one program `P`, one `g` with `g(n)/n → 0`, one exponent `K`
and one `c > 0` such that for every `n ≥ 1`, every nonsingular `B ∈ ℚ^{n×n}`, every `a ∈ ℚⁿ` and
every rational `σ² > 0` with `α η_{1/2}(L(B)) ≤ √σ²`, `SamplesDGSWithin` holds with one sample,
time `2^{α_G n + g(n)}`, space `2^{β_G n + g(n)}` and error `exp(−c n / (log(n + 2))^{2+ξ})`.

**Formalization Note.** "The constants may depend on α and ξ" (p.6): `P, g, K, c` come after
`α, ξ` and before `n` and the input. `o(n)` is one `g` for time and space; `Ω(·)` is `c·(·)` with
one `c > 0` for every `n ≥ 1` (App. C.1.4, p.81); `log` is natural (p.17). Polynomial input factors
are `(ℓ+1)^K`. `η_{1/2}` is the published `RegevLWE.GaussConv.smoothingParam`. -/
theorem theorem_1_1 (α ξ : ℝ) (hα : 1 < α) (hξ : 0 < ξ) :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ),
      Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ (a : Fin n → ℚ) (σ2 : ℚ), 0 < σ2 →
        α * RegevLWE.GaussConv.smoothingParam (latQ B) (1 / 2) ≤ Real.sqrt (σ2 : ℝ) →
        SamplesDGSWithin P K ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (3 / 2) * n + g n))
          ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (4 / 3) * n + g n))
          (Real.exp (-(c * n / Real.log ((n : ℝ) + 2) ^ (2 + ξ)))) 1 B a σ2 := by sorry

end GaussDiffSVP.Supplement
