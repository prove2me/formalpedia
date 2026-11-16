-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_12_1
-- name    : GaussDiffSVP.Supplement.theorem_12_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:51:15.666598+00:00
-- url     : https://prove2.me/theorems/9ed86a29-c2f0-4088-8933-293ac7ad9c24
-- title:
--   Theorem 12.1 — reusable $r$-BDD for $r<\sqrt{eb\log2}/(\alpha 2^{0.401})$ from Gaussian batches
-- statement:
--   Write $\alpha_G=\tfrac12\log_2(3/2)$, $\beta_G=\tfrac12\log_2(4/3)$ and $A_{KL}=2^{0.401}$. Let $(\alpha,b)$ satisfy either (125), that is $\alpha>1$ and $0<b<\min\{\beta_G,J(\alpha^{-2})\}$, or $(\alpha,b)=(3/2,\beta_G)$. For every fixed
--   $$0<r<r(\alpha,b):=\frac{\sqrt{e\,b\log2}}{\alpha A_{KL}},\tag{128}$$
--   there is an $r$-BDD data structure on every rational lattice with
--   $$P=2^{\alpha_G n+o(n)},\qquad D=2^{bn+o(n)},\qquad S=2^{\beta_G n+o(n)}.$$
--   With probability $1-o(1)$ the same advice determines a function that returns the exact nearest lattice point for every rational target at distance at most $r\lambda_1(L)$. All resource bounds hold on every execution, with polynomial input and target encoding factors suppressed.
--
--   The advice is built once per lattice from Gaussian batches on the dual and can then answer exponentially many decoding queries; at the full batch the radius supremum is $r_*\approx0.3157$.
--
--   **Formalization Note** One pair of programs, one $g$ with $g(n)/n\to0$ for the three exponents, one $K$ and one $\delta$ with $\delta(n)\to0$ are fixed after $\alpha,b,r$; the logarithm is natural and $A_{KL}=2^{401/1000}$.
--
--   Differences from the source:
--   - encoding: randomized word RAM, time in word operations, space in bits → the published randomized log-cost rational RAM TwMSOCount.Main, bit time and bit space; reason: App. C.1.1 (p.80): the same leading exponents hold with bit costs; the convention of the published goal
--   - encoding: o(n), 1 − o(1), suppressed polynomial input and target factors → one g with g(n)/n → 0, 1 − δ(n) with one δ → 0, factors (ℓ+1)^K and (ℓ+ℓ_t+1)^K; all fixed after α, b, r and before n and the input; reason: reading of the asymptotic notation as in the published goal
--   - reading: "an r-BDD data structure" (used, not formally defined in the paper) → IsBDDInterface: a preprocessing and a query program; bounds on every coin tape for every advice the preprocessing can output and every rational target; good advice = a coin-independent reply for every target and a nearest lattice point for every target at distance ≤ rλ₁(L); reason: this is the interface of §12.3 (p.59) and Theorem 12.1 (p.59): "the same advice determines a function", "a fixed resource bound even outside the promise"
--   - reading: "on every rational lattice" → every nonsingular B ∈ ℚ^{n×n}, n ≥ 1; reason: the dual-batch construction and the batch inputs are full rank, as in every other theorem of the paper
--   - reading: space S of the data structure → S bounds the bit space of the preprocessing and of every query; reason: the advice of size at most the preprocessing space is read by each query; §12.3 lists one space S
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 12.1, p.59 ((125), p.55; (128), p.59; proof App. F.1, p.103)

import Mathlib
import Definitions.Def_GaussDiffSVP_Supplement_BDD
import Definitions.Def_GaussDiffSVP_rateJ

open Filter Topology TwMSOCount.Main

namespace GaussDiffSVP.Supplement

/-- Theorem 12.1 (Decoding from a feasible Gaussian batch) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.59). Let `(α, b)` satisfy
either Equation (125) (`α > 1`, `0 < b < min{β_G, J(α^{−2})}`) or `(α, b) = (3/2, β_G)`, and put
`A_KL = 2^{0.401}`. For every fixed `0 < r < r(α, b) := √(e b log 2)/(α A_KL)` (128), there is an
`r`-BDD data structure on every rational lattice, with `P = 2^{α_G n + o(n)}`, `D = 2^{bn + o(n)}`,
`S = 2^{β_G n + o(n)}`. With probability `1 − o(1)` the same advice determines a function that
returns the exact nearest lattice point for every rational target at distance at most `rλ₁(L)`.
All resource bounds hold on every execution, with polynomial input and target encoding factors
suppressed.

**Formalization Note.** `α_G = ½ log₂(3/2)`, `β_G = ½ log₂(4/3)`, `J` is `GaussDiffSVP.rateJ`, `log`
natural, `A_KL = 2^{401/1000}`. "Every rational lattice" is every nonsingular `B ∈ ℚ^{n×n}`,
`n ≥ 1`. The data structure is a pair of programs (`IsBDDInterface`); one `g` with `g(n)/n → 0`
serves the three `o(n)`, and `1 − o(1)` is `1 − δ(n)` with one `δ → 0`, both fixed (with the
programs and `K`) after `α, b, r` and before `n` and the input. -/
theorem theorem_12_1 (α b : ℝ)
    (hαb : (1 < α ∧ 0 < b ∧ b < min (1 / 2 * Real.logb 2 (4 / 3)) (GaussDiffSVP.rateJ (α ^ 2)⁻¹)) ∨
      (α = 3 / 2 ∧ b = 1 / 2 * Real.logb 2 (4 / 3)))
    (r : ℝ) (hr0 : 0 < r)
    (hr : r < Real.sqrt (Real.exp 1 * b * Real.log 2) / (α * (2 : ℝ) ^ (401 / 1000 : ℝ))) :
    ∃ (Pre Q : Program) (g : ℕ → ℝ) (K : ℕ) (δ : ℕ → ℝ),
      Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
      IsBDDInterface r Pre Q (fun n => (2 : ℝ) ^ (1 / 2 * Real.logb 2 (3 / 2) * n + g n))
        (fun n => (2 : ℝ) ^ (b * n + g n))
        (fun n => (2 : ℝ) ^ (1 / 2 * Real.logb 2 (4 / 3) * n + g n)) K (fun n => 1 - δ n) := by sorry

end GaussDiffSVP.Supplement
