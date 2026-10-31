-- Prove2me | Theorems.Thm_GraphonLabelGame_theorem_3_6
-- name    : GraphonLabelGame.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:51.238554+00:00
-- url     : https://prove2.me/theorems/81dbbb9d-b8ea-4d5b-b3c4-af54decb7d40
-- title:
--   Theorem 3.6 (General kernel) — graphon equilibrium controls give $n$-player $\epsilon$-Nash equilibria with $\frac1n\sum_i\mathbb E[\epsilon^n_i(U^n)]\to0$
-- statement:
--   Assume the standing assumptions of §3. Let $W\in L^1_+[0,1]^2$ (not necessarily bounded or symmetric), let $\mu_\cdot\in C([0,T];\mathcal P_{\mathrm{Unif}}([0,1]\times\mathbb R^d))$ be a $W$-equilibrium with equilibrium control $\alpha^*$, and assume the disintegration $u\mapsto\lambda_u$ of the initial law admits a version such that $\{\lambda_u:u\in[0,1]\}$ is tight. Let $\xi^n$ be $n\times n$ matrices with nonnegative entries and zero diagonal such that $W_{\xi^n}\to W$ in the strong operator topology and
--   $$\lim_{n\to\infty}\frac1{n^3}\sum_{i,j=1}^n(\xi^n_{ij})^2=0.\tag{3.9}$$
--   Give player $i$ the label $u^n_i$, the control $\alpha^*(t,u^n_i,x_i)$ and an independent initial state $X^{n,i}_0\sim\lambda_{u^n_i}$, and let $\epsilon^n_i(u^n)$ be the largest gain player $i$ can obtain by a unilateral deviation $\beta\in\mathcal A_n$. If for each $n$ the labels $U^n_1,\dots,U^n_n$ are independent with $U^n_i\sim\mathrm{Unif}(I^n_i)$, then
--   $$\lim_{n\to\infty}\frac1n\sum_{i=1}^n\mathbb E\big[\epsilon^n_i(U^n_1,\dots,U^n_n)\big]=0.$$
--
--   So a single graphon equilibrium yields approximate Nash equilibria, in an averaged sense, for every sequence of large weighted directed networks converging to $W$ in the strong operator topology (in particular in cut norm), including sparse ones.
--
--   Differences from the source:
--   - reading: "an arbitrary n×n matrix ξⁿ with positive entries and zeros on the diagonal" (§3.4, p.10) → IsInteractionMatrix: ξⁿᵢⱼ ≥ 0 and ξⁿᵢᵢ = 0; reason: positive entries contradict a zero diagonal; §3.1 (p.7) says nonnegative entries
--   - reading: E[εⁿᵢ(Uⁿ₁, …, Uⁿₙ)] (εⁿᵢ not shown measurable) → the outer integral of εⁿᵢ against the uniform law on Iⁿ₁ × ⋯ × Iⁿₙ; reason: the strongest reading: it dominates every value the expectation could be given, and equals the ordinary integral when εⁿᵢ is measurable
--   - encoding: εⁿᵢ(uⁿ) ∈ [0, ∞) (p.11) → eps: ℝ≥0∞-valued supremum over β ∈ 𝒜ₙ, solutions of the deviated and of the undeviated system of (Jᵢ(S') − Jᵢ(S))⁺; the limit taken in ℝ≥0∞; reason: the printed difference is ≥ 0 (take β = αᵢ), so the positive part changes nothing; εⁿᵢ is bounded
--   - encoding: "Assume the disintegration u ↦ λᵤ admits a version such that {λᵤ : u ∈ [0,1]} is tight"; εⁿᵢ defined from that version (p.11) → a Markov kernel κ with {κ(u) : u ∈ [0,1]} tight, λ := Unif[0,1] ⊗ κ, and εⁿᵢ computed with X^{n,i}_0 ∼ κ(uᵢ); reason: every λ ∈ P_Unif has a measurable version; the statement holds for every tight one
--   - encoding: μ· is a W-equilibrium with equilibrium control α* (Definition 3.1) → IsWEquilibrium: α* ∈ 𝒜_U, μ· continuous P_Unif-valued, some solution S* under α* has L(U, X_t) = μ_t for t ∈ [0,T], and J_W(S) ≤ J_W(S*) for every α ∈ 𝒜_U and every solution S under α; reason: Definition 3.1 relation-wise; the ∃ S* form is no stronger than the paper's (solutions are unique in law)
--   - reading: "σ is Lipschitz" (p.6) → σ(t,·) Lipschitz in x with one constant for all t ∈ [0,T] (entrywise); reason: the weaker of the two readings, hence the stronger theorem; well-posedness via [49, Theorem 1] (pp.7–8) needs only this
--   - encoding: standing assumptions of §3 (p.6): b, σ, f, g bounded continuous on [0,T] × ⋯ → Data.Standing: ContinuousOn and bounded on Iic T × ⋯, M₊(ℝᵈ) = FiniteMeasure with the weak topology; reason: the functions are only used on [0,T]
--   - encoding: d, d₀ ∈ ℕ, T > 0 (p.6) → 1 ≤ d and 0 < T; d₀ ≥ 1 is not stated separately; reason: the paper's ℕ starts at 1; d₀ ≥ 1 follows from σσᵀ ≥ c·I with c > 0 and d ≥ 1
--   - encoding: "the unique solution" of the state SDE (pp.7–8, 21) → solutions are a relation (GSol / NSol: a filtered probability space with an F-Brownian motion and a continuous adapted state satisfying the Itô equation); statements quantify over all solutions; reason: under the standing assumptions solutions exist and are unique in law ([49] cited p.7), so every payoff equals the paper's
--   - encoding: a given filtered probability space (Ω, F, 𝔽, P) (p.8), B¹,…,Bⁿ independent Brownian motions (p.7) → any probability space with a filtration for which the Brownian motion(s) are adapted with increments independent of the past; filtration not augmented; Itô integrals in the sense of Peng1990.SMP.IsItoIntegral; reason: payoffs depend only on the law of the solution, which is unique in law
--   - encoding: time t ∈ [0,T], labels u ∈ [0,1], ℝᵈ, C^d = C([0,T];ℝᵈ) → time ℝ≥0 read on [0,T] (paths clamped at T), labels in ℝ, ℝᵈ = Fin d → ℝ (sup norm), C^d = C(Icc 0 T, Fin d → ℝ) with its Borel σ-field; reason: Lean conventions; only t ∈ [0,T] and u ∈ [0,1] enter, and the norms on ℝᵈ give the same topology
--   - encoding: measurable controls on [0,T] × [0,1] × ℝᵈ (𝒜_U), [0,T] × ℝᵈ (𝒜₁), [0,T] × (ℝᵈ)ⁿ (𝒜ₙ) → measurable maps on ℝ≥0 × ℝ × ℝᵈ, ℝ≥0 × ℝᵈ, ℝ≥0 × (ℝᵈ)ⁿ; reason: every control on the smaller domain extends measurably; values outside never enter
--   - encoding: 𝐖m(u) ∈ M₊(E) (2.6) → Wop W m u, set to 0 at the labels u where ∫W(u,v)m(dv,dx) = ∞; reason: for m with uniform first marginal these labels form a Lebesgue-null set (Fubini, p.15), which no expectation over a uniform label sees
--   - encoding: Iⁿᵢ = [(i−1)/n, i/n) for i < n and Iⁿₙ = [(n−1)/n, 1] (2.1); §6.1 prints the half-open form for all i → I n i with i : Fin n counted from 0, the last interval closed; reason: (2.1) is the definition; the two forms differ by a null set
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, Theorem 3.6, p.11 (standing assumptions p.6; §3.1 p.7; §3.2 p.8; §3.4 pp.10–11)

import Mathlib
import Definitions.Def_GraphonLabelGame_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **Theorem 3.6 (General kernel)**. Lacker–Soret, arXiv:2204.09642v1, Theorem 3.6, p.11
(setting §3, p.6; §3.1, p.7; §3.2, p.8; §3.4, pp.10–11). Under the standing assumptions, let
`W ∈ L¹₊[0, 1]²`, let `μ·` be a `W`-equilibrium with equilibrium control `α*`, and assume the
disintegration `u ↦ λᵤ` of the initial law admits a version `κ` with `{λᵤ : u ∈ [0, 1]}` tight.
Let `ξⁿ` be `n × n` matrices with nonnegative entries and zero diagonal such that
`W_{ξⁿ} → W` in the strong operator topology and `(1/n³) Σᵢⱼ (ξⁿᵢⱼ)² → 0` (3.9). If
`Uⁿ₁, …, Uⁿₙ` are independent with `Uⁿᵢ ∼ Unif(Iⁿᵢ)`, then
`lim_n (1/n) Σᵢ E[εⁿᵢ(Uⁿ₁, …, Uⁿₙ)] = 0`.

**Formalization Note** The initial law is `λ = Unif[0, 1] ⊗ κ` for the given version `κ`, and
`εⁿᵢ` is computed with initial states `X^{n,i}_0 ∼ κ(uᵢ)` (p.11). `εⁿᵢ` is valued in `ℝ≥0∞`, and
`E[εⁿᵢ(Uⁿ)]` is the outer integral against the uniform law on `Iⁿ₁ × ⋯ × Iⁿₙ` (the paper does not
show `εⁿᵢ` measurable). -/
theorem theorem_3_6 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (κ : Kernel ℝ (Fin d → ℝ)) [IsMarkovKernel κ]
    (hκ : IsTightMeasureSet ((fun u => κ u) '' Icc (0 : ℝ) 1))
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A)
    (heq : IsWEquilibrium D W (lamOf κ) μ αs)
    (ξ : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (hξ : ∀ n, IsInteractionMatrix (ξ n))
    (hSOT : SOTConv (fun n => stepKernel (ξ n)) W)
    (h39 : Tendsto (fun n : ℕ => (1 / (n : ℝ) ^ 3) * ∑ i, ∑ j, (ξ n i j) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ≥0∞)) *
        ∑ i : Fin n, outerLIntegral (unifBox n) (fun u => eps D (ξ n) αs κ u i)) atTop
      (𝓝 0) := by sorry

end GraphonLabelGame
