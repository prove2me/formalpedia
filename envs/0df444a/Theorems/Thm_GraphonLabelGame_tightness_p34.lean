-- Prove2me | Theorems.Thm_GraphonLabelGame_tightness_p34
-- name    : GraphonLabelGame.tightness_p34
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:25.804992+00:00
-- url     : https://prove2.me/theorems/120ff8a7-54ce-4205-96d4-daa6208e814b
-- title:
--   Tightness of the deviating players' laws $\{\mathcal L(X^{n,\beta,u^n_i,i})\}$ in $\mathcal P(\mathcal C^d)$ (p.34)
-- statement:
--   Assume the standing assumptions of §3. Let $\alpha^*\in\mathcal A_U$ and assume the disintegration $u\mapsto\lambda_u$ of the initial law has a version with $\{\lambda_u:u\in[0,1]\}$ tight. For $n\in\mathbb N$, labels $u^n\in[0,1]^n$, $i\in[n]$ and $\beta\in\mathcal A_n$, let $X^{n,\beta,u^n_i,i}$ be player $i$'s state in the $n$-player system in which player $i$ uses $\beta$, every other player $j$ uses $\alpha^*(t,u^n_j,x_j)$, and the initial states $X^{n,j}_0\sim\lambda_{u^n_j}$ are independent (7.2). Then
--   $$\big\{\mathcal L(X^{n,\beta,u^n_i,i}):n\in\mathbb N,\ \beta\in\mathcal A_n,\ u^n\in[0,1]^n,\ i\in[n]\big\}$$
--   is a tight subset of $\mathcal P(\mathcal C^d)$, $\mathcal C^d=C([0,T];\mathbb R^d)$.
--
--   Tightness localizes the reward differences $\Delta^{n,i}_1$ and $\Delta^{n,i}_3$ to a compact set of paths, uniformly over players, labels and deviations.
--
--   Differences from the source:
--   - generalization: α* the equilibrium control of μ· → any α* ∈ 𝒜_U; reason: the argument uses only boundedness of b, σ and tightness of {λᵤ}; specializes to the equilibrium control
--   - encoding: the set of laws L(X^{n,β,uⁿᵢ,i}) → the laws P ∘ (Xⁱ)⁻¹ on C^d of player i's state over all solutions of all deviated systems; reason: relation form; solutions are unique in law
--   - encoding: the initial law λ ∈ P_Unif([0,1] × ℝᵈ) with disintegration λ(du,dx) = du λᵤ(dx) (pp.4, 11) → a Markov kernel κ (a measurable version of u ↦ λᵤ) with λ := Unif[0,1] ⊗ κ; reason: every λ ∈ P_Unif has such a version; the statement holds for every version
--   - reading: "σ is Lipschitz" (p.6) → σ(t,·) Lipschitz in x with one constant for all t ∈ [0,T] (entrywise); reason: the weaker of the two readings, hence the stronger theorem; well-posedness via [49, Theorem 1] (pp.7–8) needs only this
--   - encoding: standing assumptions of §3 (p.6): b, σ, f, g bounded continuous on [0,T] × ⋯ → Data.Standing: ContinuousOn and bounded on Iic T × ⋯, M₊(ℝᵈ) = FiniteMeasure with the weak topology; reason: the functions are only used on [0,T]
--   - encoding: d, d₀ ∈ ℕ, T > 0 (p.6) → 1 ≤ d and 0 < T; d₀ ≥ 1 is not stated separately; reason: the paper's ℕ starts at 1; d₀ ≥ 1 follows from σσᵀ ≥ c·I with c > 0 and d ≥ 1
--   - encoding: "the unique solution" of the state SDE (pp.7–8, 21) → solutions are a relation (GSol / NSol: a filtered probability space with an F-Brownian motion and a continuous adapted state satisfying the Itô equation); statements quantify over all solutions; reason: under the standing assumptions solutions exist and are unique in law ([49] cited p.7), so every payoff equals the paper's
--   - encoding: a given filtered probability space (Ω, F, 𝔽, P) (p.8), B¹,…,Bⁿ independent Brownian motions (p.7) → any probability space with a filtration for which the Brownian motion(s) are adapted with increments independent of the past; filtration not augmented; Itô integrals in the sense of Peng1990.SMP.IsItoIntegral; reason: payoffs depend only on the law of the solution, which is unique in law
--   - encoding: time t ∈ [0,T], labels u ∈ [0,1], ℝᵈ, C^d = C([0,T];ℝᵈ) → time ℝ≥0 read on [0,T] (paths clamped at T), labels in ℝ, ℝᵈ = Fin d → ℝ (sup norm), C^d = C(Icc 0 T, Fin d → ℝ) with its Borel σ-field; reason: Lean conventions; only t ∈ [0,T] and u ∈ [0,1] enter, and the norms on ℝᵈ give the same topology
--   - encoding: measurable controls on [0,T] × [0,1] × ℝᵈ (𝒜_U), [0,T] × ℝᵈ (𝒜₁), [0,T] × (ℝᵈ)ⁿ (𝒜ₙ) → measurable maps on ℝ≥0 × ℝ × ℝᵈ, ℝ≥0 × ℝᵈ, ℝ≥0 × (ℝᵈ)ⁿ; reason: every control on the smaller domain extends measurably; values outside never enter
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, §7, p.34 ("First, note that {λᵤ : u ∈ [0,1]} is tight. … is a tight subset of P(C^d)")

import Mathlib
import Definitions.Def_GraphonLabelGame_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **Tightness of the deviating players' laws** (§7, p.34). Lacker–Soret,
arXiv:2204.09642v1, p.34. Under the standing assumptions, let `α* ∈ 𝒜_U` and let `κ` be a
version of `u ↦ λᵤ` with `{λᵤ : u ∈ [0, 1]}` tight. Then the set of laws
`{L(X^{n,β,uⁿᵢ,i}) : n ∈ ℕ, β ∈ 𝒜ₙ, uⁿ ∈ [0, 1]ⁿ, i ∈ [n]}` is a tight subset of `P(C^d)`,
`C^d = C([0, T]; ℝᵈ)`, where `X^{n,β,uⁿᵢ,i}` is player `i`'s state in (7.2): player `i` uses
`β`, every other player `j` uses `α*(t, uⱼ, xⱼ)`, and `X^{n,j}_0 ∼ λ_{uⱼ}` independently.

**Formalization Note** The set ranges over all solutions of all deviated systems. -/
theorem tightness_p34 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (κ : Kernel ℝ (Fin d → ℝ)) [IsMarkovKernel κ]
    (hκ : IsTightMeasureSet ((fun u => κ u) '' Icc (0 : ℝ) 1))
    (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A) (hαs : IsUControl αs) :
    IsTightMeasureSet {ν : Measure (Path d D.T) | ∃ (n : ℕ) (u : Fin n → ℝ)
      (_ : ∀ j, u j ∈ Icc (0 : ℝ) 1) (i : Fin n) (β : ℝ≥0 → (Fin n → Fin d → ℝ) → A)
      (_ : IsNControl β) (S : NSol D n (Function.update (labelProfile αs u) i β) κ u),
      ν = S.P.map (fun ω => S.X ω i)} := by sorry

end GraphonLabelGame
