-- Prove2me | Theorems.Thm_GMMPostSamp_Main_theorem_3
-- name    : GMMPostSamp.Main.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:29:05.888192+00:00
-- url     : https://prove2.me/theorems/3fca39fb-bd6c-407c-9426-70e15624ccd9
-- title:
--   Theorem 3 — a polynomial-time sampler within TV δ of the label posterior of Model 1, for every σ > 0 and α ∈ [a, A]^k
-- statement:
--   Let $\mathrm{Law}_P(x_{[n]})$ be the output law of a program $P$ on input $(k,d,n,\sigma,\delta,\alpha,x_{[n]})$ and $\pi_x$ the label posterior of Model 1. There are one admissible program $P$ and one universal constant $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$ and $\delta\in(0,\frac12)$, with
--   $$\tau:=\frac1{Ak}\Big(\frac{\delta^2}{192k}\Big)^{1/a},$$
--   if $d\ge C(k+\log\frac1\delta)$ and
--   $$n\ge C\,\frac{d^3k^{11}(1+\sigma^{20})}{\tau^{10}}\Big(\frac1{\tau^6}+\log^6d\Big),$$
--   then (i) for every $x_{[n]}\in(\mathbb R^d)^n$, every run of $P$ halts within $C\,\frac{nd^2k^2(1+\sigma^6)}{\tau^4}\log^4\frac n\delta+C$ steps, and (ii)
--   $$\Pr_{x_{[n]}\sim\text{Model 1}}\Big[\mathrm{TV}\big(\mathrm{Law}_P(x_{[n]}),\pi_x\big)>\delta\Big]\le\delta.$$
--   This is the paper's main result: posterior sampling of cluster labels in polynomial time at every noise level, including below the threshold where clustering is impossible.
--
--   **Formalization Note.** $P$ does not receive $a$, $A$, $\tau$, $\theta^\star$ or the posterior; it runs on the machine of the Machine definition (no eigensolver primitive).
--
--   Differences from the source:
--   - reading: n = Ω(…), d = Ω(k + log 1/δ), time O(…), 'for appropriate constants' → one universal C > 0 quantified before k, d, n, σ, a, A, α, δ: d ≥ C(k + log(1/δ)), n ≥ C·(…), every run within C·(…) + C steps; reason: each Ω(·)/O(·) is an explicit universal constant; + C covers the constant cost
--   - encoding: an algorithm in the real RAM model of §2.1 → an admissible program on the Machine definition (SmaleNinth core, √, exp, log, Γ, Unif[0,1] and N(0,1) tapes, CDF/quantile of N, Beta, noncentral χ²); reason: the reading of §2.1 fixed in the Machine definition
--   - encoding: the algorithm runs in time O(…) → every run (every tape pair in the support) on every x_[n] ∈ (ℝ^d)^n halts within the bound; reason: worst-case runtime
--   - encoding: P[TV(Law(ι_[n]), π) ≤ δ] ≥ 1 − δ over Model 1 → Model-1 (outer) measure of {x : TV(Law_P(x), π_x) > δ} ≤ δ; π_x by Bayes' rule for every x; output on Option ([k]^n) with none counted against TV; reason: Problem 1; the posterior is defined everywhere so the failure set is unambiguous
--   - reading: Model 1: (k, d, n) ∈ N³, ι⋆_j ∼ Cat(w), x_j | ι⋆_j ∼ N(µ_{ι⋆_j}, σ²I_d); k, d, n, σ, α known → k, d, n ≥ 1; Cat(w⋆), N(µ⋆_{ι⋆_j}, σ²I_d); the program receives (k, d, n, σ, δ, α, x_[n]) but not a, A; reason: notational slip in Model 1; the algorithm knows exactly what Model 1 says it knows
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 26, Theorem 3

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Theorem 3 (p. 26): there are one randomized real-RAM program `P` and one universal constant
`C > 0` such that for all `k, d, n ≥ 1`, `σ > 0`, `0 < a ≤ A`, `α ∈ [a, A]^k` and
`δ ∈ (0, 1/2)`, with `τ = (1/(Ak))(δ²/(192k))^{1/a}`: if `d ≥ C(k + log(1/δ))` and
`n ≥ C d³k¹¹(1 + σ²⁰)/τ¹⁰ · (1/τ⁶ + log⁶ d)`, then every run of `P` on
`(k, d, n, σ, δ, α, x_[n])`, for every `x_[n]`, halts within
`C nd²k²(1 + σ⁶)/τ⁴ · log⁴(n/δ) + C` steps, and the Model-1 probability of the observations on
which the output law is more than `δ` from the label posterior in TV is at most `δ`. -/
theorem theorem_3 : ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → 0 < δ → δ < 1 / 2 →
      let τ : ℝ := (1 / (A * k)) * (δ ^ 2 / (192 * k)) ^ (1 / a)
      C * ((k : ℝ) + Real.log (1 / δ)) ≤ d →
      C * ((d : ℝ) ^ 3 * (k : ℝ) ^ 11 * (1 + σ ^ 20) / τ ^ 10 *
          (1 / τ ^ 6 + Real.log d ^ 6)) ≤ n →
      (∀ x : Fin n → E d, Machine.HaltsWithin P (Machine.samplerInput σ δ α x)
          (C * (n * (d : ℝ) ^ 2 * (k : ℝ) ^ 2 * (1 + σ ^ 6) / τ ^ 4 * Real.log (n / δ) ^ 4)
            + C)) ∧
      Machine.SolvesProblem1 P k d n σ α δ := by sorry

end GMMPostSamp.Main
