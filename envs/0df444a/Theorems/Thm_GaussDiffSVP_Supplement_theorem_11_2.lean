-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_11_2
-- name    : GaussDiffSVP.Supplement.theorem_11_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:50:10.447704+00:00
-- url     : https://prove2.me/theorems/2bf5448c-7f3c-46a7-b0e6-e923b027fd58
-- title:
--   Theorem 11.2 — batches of $\lfloor 2^{bn}\rfloor$ discrete Gaussian samples for $b<\min\{\beta_G,J(\alpha^{-2})\}$
-- statement:
--   Write $\alpha_G=\tfrac12\log_2(3/2)$, $\beta_G=\tfrac12\log_2(4/3)$ and $J(z)=\frac{z-1-\log z}{2\log2}$. Fix $\alpha>1$ and
--   $$0<b<\min\{\beta_G,\,J(\alpha^{-2})\}.\tag{125}$$
--   Given a full rank rational lattice $L=B\mathbb Z^n$, a rational shift $a$ and a positive rational squared width $\sigma^2$ with $\sigma\ge\alpha\eta_{1/2}(L)$, there is an algorithm producing $\lfloor2^{bn}\rfloor$ points of $a+L$ whose joint law is within
--   $$\exp\!\big[-\Omega\big(n/\log^2(n+2)\big)\big]$$
--   in total variation of the product law $D_{a+L,\sigma}^{\otimes\lfloor2^{bn}\rfloor}$, in time $2^{\alpha_G n+o(n)}$ and bit space $2^{\beta_G n+o(n)}$ (the space includes the output).
--
--   This is the general batch theorem; smaller batches allow a narrower width and feed the GapSVP application of §12.
--
--   **Formalization Note** One program, $g$, $K$ and $c>0$ are fixed after $\alpha,b$; $J$ is the published rateJ; the batch size is $\lfloor2^{bn}\rfloor$ as a natural number.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - encoding: o(n), exp[−Ω(·)], suppressed polynomial factors in the input length → one g with g(n)/n → 0, exp(−c·(·)) with one c > 0 for every n ≥ 1, a factor (ℓ+1)^K; program, g, K, c fixed after the fixed parameters and before n and the input; reason: reading of the asymptotic notation as in the published goal; App. C.1.4 (p.81) covers the finitely many small ranks
--   - encoding: output points X ∈ a + L and their law → rational coordinate words, every output on every coin tape a tuple of points of a + L, total variation ½Σ over output words; reason: points of a + L are rational and the word encoding is injective, so the laws correspond
--   - encoding: η_ε(L) defined by ρ_{1/η}(L*∖{0}) = ε → the published smoothingParam, the infimum of s > 0 with ρ_{1/s}(L*∖{0}) ≤ ε; reason: the dual mass is continuous and strictly decreasing in s, so both give the same value
--   - encoding: a full rank rational lattice L = Bℤⁿ → a nonsingular B ∈ ℚ^{n×n}, n ≥ 1; reason: same instances; the rank-0 lattice is excluded as in the published goal
--   - reading: "On the inputs of Theorem 1.2" → a nonsingular B ∈ ℚ^{n×n}, a ∈ ℚⁿ and a rational σ² > 0 with α η_{1/2}(L) ≤ σ, as listed in Theorem 1.2 (p.6); reason: Theorem 1.2 names exactly these inputs and the width promise
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 11.2, p.55 ((125), p.55; inputs of Theorem 1.2, p.6)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_DGS
import Definitions.Def_GaussDiffSVP_rateJ

open Filter Topology TwMSOCount.Main CosetTreeSVP.SVP

namespace GaussDiffSVP.Supplement

/-- Theorem 11.2 (Batches with independently chosen extensions) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.55). Fix `α > 1` and
`0 < b < min{β_G, J(α^{−2})}` (125). On the inputs of Theorem 1.2 (a full rank rational lattice
`L = Bℤⁿ`, a rational shift `a`, a positive rational squared width `σ²` with `σ ≥ αη_{1/2}(L)`,
p.6), there is an algorithm producing `⌊2^{bn}⌋` points with joint statistical distance at most
`exp[−Ω(n / log²(n + 2))]` from the target product distribution `D_{a+L,σ}^{⊗⌊2^{bn}⌋}`, in time
`2^{α_G n + o(n)}` and bit space `2^{β_G n + o(n)}` (including the output, p.6).

**Formalization Note.** `α_G = ½ log₂(3/2)`, `β_G = ½ log₂(4/3)`, `J` is the published
`GaussDiffSVP.rateJ`; `P, g, K, c` are fixed after `α, b` and before `n` and the input, `o(n)` is
one `g`, `Ω(·)` is `c·(·)` with one `c > 0` for every `n ≥ 1`, `log` natural. The batch size is
`Nat.floor (2^{bn})`; points of `a + L` are output by their rational coordinates. -/
theorem theorem_11_2 (α b : ℝ) (hα : 1 < α) (hb0 : 0 < b)
    (hb : b < min (1 / 2 * Real.logb 2 (4 / 3)) (GaussDiffSVP.rateJ (α ^ 2)⁻¹)) :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ),
      Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
      ∀ (a : Fin n → ℚ) (σ2 : ℚ), 0 < σ2 →
        α * RegevLWE.GaussConv.smoothingParam (latQ B) (1 / 2) ≤ Real.sqrt (σ2 : ℝ) →
        SamplesDGSWithin P K ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (3 / 2) * n + g n))
          ((2 : ℝ) ^ (1 / 2 * Real.logb 2 (4 / 3) * n + g n))
          (Real.exp (-(c * n / Real.log ((n : ℝ) + 2) ^ 2)))
          ⌊(2 : ℝ) ^ (b * n)⌋₊ B a σ2 := by sorry

end GaussDiffSVP.Supplement
