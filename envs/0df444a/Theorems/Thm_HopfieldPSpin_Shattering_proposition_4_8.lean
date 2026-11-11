-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_proposition_4_8
-- name    : HopfieldPSpin.Shattering.proposition_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:45.786524+00:00
-- url     : https://prove2.me/theorems/d64eea7e-4b5e-4afa-9f99-ce87d700125e
-- title:
--   Proposition 4.8 — one-pattern truncated Laplace expansion $\mathbb E[e^{tY}\mathbf 1_{E_1}]=1+\frac{t^2}2\mathbb EY^2+O(|t|^3)+\rho_n$
-- statement:
--   Fix $0<\alpha_-<\alpha_+<\infty$ and $0\le S<\infty$. There is $p_0=p_0(\alpha_-,\alpha_+,S)\ge5$ such that for every fixed integer $p\ge p_0$: if $\alpha_-n^{p-1}\le M_n\le\alpha_+n^{p-1}$ for all large $n$, then for $t=s\sqrt{n/M_n}$, $|s|\le S$, and $Y=X_1(\sigma)$ or $Y=X_1(\sigma)+X_1(\tau)$,
--   $$\mathbb E[e^{tY}\mathbf 1_{E_1}]=1+\frac{t^2}2\,\mathbb EY^2+O(|t|^3)+\rho_n ,$$
--   where both errors are uniform in $s,\sigma,\tau$ and the choice of $Y$, the constant in $O(|t|^3)$ depends only on $p,\alpha_-,\alpha_+,S$, and $\rho_n=o(n^{-A})$ for every fixed $A>0$.
--
--   Formally: there is $C$ (chosen before the storage sequence and the law) and, for each storage sequence and law, a sequence $\rho_n$ with $n^A\rho_n\to0$ for every $A>0$ such that for all large $n$ the error is at most $C|t|^3+\rho_n$, simultaneously for all $|s|\le S$, $\sigma,\tau$ and both choices of $Y$.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - generalization: pattern index $1$ ($X_1$, $E_1$) → every pattern index $k$ ($X_k$, $E_k$); reason: all patterns are identically distributed; $k=1$ is an instance
--   - encoding: $O(|t|^3)+\rho_n$ uniform, $\rho_n=o(n^{-A})$ for every $A>0$ → ∃ C before the storage sequence and the law, ∃ ρ with $n^A\rho_n\to0$ ∀ A > 0, and eventually $|\mathbb E[e^{tY}\mathbf 1_{E_k}]-1-\frac{t^2}2\mathbb EY^2|\le C|t|^3+\rho_n$ for all $|s|\le S$, σ, τ, Y; reason: the paper's uniform $O$ and $o$; the pattern law is quantified as in the standing assumptions
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 19 (PDF 21), Proposition 4.8, (4.13)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Proposition 4.8 (p. 19): one-pattern truncated Laplace expansion
`E[e^{tY} 1_{E_1}] = 1 + (t²/2) E Y² + O(|t|³) + ρ_n`, `t = s √(n/M_n)`, `|s| ≤ S`,
`Y = X_1(σ)` or `X_1(σ) + X_1(τ)`, with the `O`-constant depending only on
`p, α₋, α₊, S` and `ρ_n = o(n^{−A})` for every `A > 0`, both uniform in `s, σ, τ, Y`. -/
theorem proposition_4_8 (αm αp S : ℝ) (hαm : 0 < αm) (hα : αm < αp) (hS : 0 ≤ S) :
    ∃ p₀ : ℕ, 5 ≤ p₀ ∧ ∀ p : ℕ, p₀ ≤ p → ∃ C : ℝ, ∀ M : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, αm * (n : ℝ) ^ (p - 1) ≤ (M n : ℝ) ∧ (M n : ℝ) ≤ αp * (n : ℝ) ^ (p - 1)) →
      ∀ law : PatternLaw, ∃ ρ : ℕ → ℝ,
        (∀ A : ℝ, 0 < A → Tendsto (fun n : ℕ => (n : ℝ) ^ A * ρ n) atTop (𝓝 0)) ∧
        ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, |s| ≤ S → ∀ σ τ : Config n, ∀ k : Fin (M n),
          ∀ Y : (Fin (M n) → Fin n → ℝ) → ℝ,
            (Y = (fun η => patternField n (M n) p η k σ) ∨
              Y = (fun η => patternField n (M n) p η k σ + patternField n (M n) p η k τ)) →
            |(∫ η, (normEvent n (M n) k).indicator
                  (fun η => Real.exp (s * Real.sqrt ((n : ℝ) / (M n : ℝ)) * Y η)) η
                  ∂(disorderLaw n (M n) law)) -
                1 - (s * Real.sqrt ((n : ℝ) / (M n : ℝ))) ^ 2 / 2 *
                  ∫ η, Y η ^ 2 ∂(disorderLaw n (M n) law)| ≤
              C * |s * Real.sqrt ((n : ℝ) / (M n : ℝ))| ^ 3 + ρ n := by sorry

end HopfieldPSpin.Shattering
