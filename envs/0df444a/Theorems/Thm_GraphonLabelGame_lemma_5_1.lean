-- Prove2me | Theorems.Thm_GraphonLabelGame_lemma_5_1
-- name    : GraphonLabelGame.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:36.226797+00:00
-- url     : https://prove2.me/theorems/01f7d1a7-38c8-46bf-8809-65474221b593
-- title:
--   Lemma 5.1 — an optimal control stays optimal for almost every frozen label
-- statement:
--   Assume the standing assumptions of §3. Let $W\in L^1_+[0,1]^2$, $\mu_\cdot\in C([0,T];\mathcal P_{\mathrm{Unif}}([0,1]\times\mathbb R^d))$, and let $\lambda(du,dx)=du\,\lambda_u(dx)$ be the initial law. Suppose $\alpha\in\mathcal A_U$ satisfies $J_W(\mu_\cdot,\alpha)\ge J_W(\mu_\cdot,\beta)$ for all $\beta\in\mathcal A_U$. Then
--   $$J^{u,\lambda_u}_W(\mu_\cdot,\alpha_u)=\sup_{\beta\in\mathcal A_1}J^{u,\lambda_u}_W(\mu_\cdot,\beta)\qquad\text{for a.e. }u\in[0,1],$$
--   where $\alpha_u\in\mathcal A_1$ is defined by $\alpha_u(t,x)=\alpha(t,u,x)$.
--
--   In words: if a label-dependent feedback is optimal for the randomized label, it is optimal for almost every fixed label. This is the step that turns the equilibrium property of $\alpha^*$ into the bound $\Delta^{n,i}_2\le0$ of Lemma 7.1.
--
--   Differences from the source:
--   - encoding: J_W(μ·, α) ≥ J_W(μ·, β) for all β ∈ 𝒜_U → some solution Sα under α has J_W(S) ≤ J_W(Sα) for every β ∈ 𝒜_U and every solution S under β; reason: relation form; no stronger than the paper's hypothesis since solutions exist and are unique in law
--   - encoding: J^{u,λᵤ}_W(μ·, αᵤ) = sup_{β∈𝒜₁} J^{u,λᵤ}_W(μ·, β) → every solution under αᵤ with initial law δᵤ × λᵤ has reward ≥ that of every solution under every β ∈ 𝒜₁; reason: relation form of the equality; solutions are unique in law
--   - encoding: the initial law λ ∈ P_Unif([0,1] × ℝᵈ) with disintegration λ(du,dx) = du λᵤ(dx) (pp.4, 11) → a Markov kernel κ (a measurable version of u ↦ λᵤ) with λ := Unif[0,1] ⊗ κ; reason: every λ ∈ P_Unif has such a version; the statement holds for every version
--   - reading: "σ is Lipschitz" (p.6) → σ(t,·) Lipschitz in x with one constant for all t ∈ [0,T] (entrywise); reason: the weaker of the two readings, hence the stronger theorem; well-posedness via [49, Theorem 1] (pp.7–8) needs only this
--   - encoding: standing assumptions of §3 (p.6): b, σ, f, g bounded continuous on [0,T] × ⋯ → Data.Standing: ContinuousOn and bounded on Iic T × ⋯, M₊(ℝᵈ) = FiniteMeasure with the weak topology; reason: the functions are only used on [0,T]
--   - encoding: d, d₀ ∈ ℕ, T > 0 (p.6) → 1 ≤ d and 0 < T; d₀ ≥ 1 is not stated separately; reason: the paper's ℕ starts at 1; d₀ ≥ 1 follows from σσᵀ ≥ c·I with c > 0 and d ≥ 1
--   - encoding: "the unique solution" of the state SDE (pp.7–8, 21) → solutions are a relation (GSol / NSol: a filtered probability space with an F-Brownian motion and a continuous adapted state satisfying the Itô equation); statements quantify over all solutions; reason: under the standing assumptions solutions exist and are unique in law ([49] cited p.7), so every payoff equals the paper's
--   - encoding: a given filtered probability space (Ω, F, 𝔽, P) (p.8), B¹,…,Bⁿ independent Brownian motions (p.7) → any probability space with a filtration for which the Brownian motion(s) are adapted with increments independent of the past; filtration not augmented; Itô integrals in the sense of Peng1990.SMP.IsItoIntegral; reason: payoffs depend only on the law of the solution, which is unique in law
--   - encoding: time t ∈ [0,T], labels u ∈ [0,1], ℝᵈ, C^d = C([0,T];ℝᵈ) → time ℝ≥0 read on [0,T] (paths clamped at T), labels in ℝ, ℝᵈ = Fin d → ℝ (sup norm), C^d = C(Icc 0 T, Fin d → ℝ) with its Borel σ-field; reason: Lean conventions; only t ∈ [0,T] and u ∈ [0,1] enter, and the norms on ℝᵈ give the same topology
--   - encoding: measurable controls on [0,T] × [0,1] × ℝᵈ (𝒜_U), [0,T] × ℝᵈ (𝒜₁), [0,T] × (ℝᵈ)ⁿ (𝒜ₙ) → measurable maps on ℝ≥0 × ℝ × ℝᵈ, ℝ≥0 × ℝᵈ, ℝ≥0 × (ℝᵈ)ⁿ; reason: every control on the smaller domain extends measurably; values outside never enter
--   - encoding: 𝐖m(u) ∈ M₊(E) (2.6) → Wop W m u, set to 0 at the labels u where ∫W(u,v)m(dv,dx) = ∞; reason: for m with uniform first marginal these labels form a Lebesgue-null set (Fubini, p.15), which no expectation over a uniform label sees
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, Lemma 5.1, p.22 (J^{u,m}_W defined on p.21)

import Mathlib
import Definitions.Def_GraphonLabelGame_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **Lemma 5.1**. Lacker–Soret, arXiv:2204.09642v1, Lemma 5.1, p.22. Under the standing
assumptions, let `W ∈ L¹₊[0, 1]²`, `μ· ∈ C([0, T]; P_Unif([0, 1] × ℝᵈ))`, and let `κ` be a
version of the disintegration `u ↦ λᵤ` of the initial law `λ`. Suppose `α ∈ 𝒜_U` satisfies
`J_W(μ·, α) ≥ J_W(μ·, β)` for all `β ∈ 𝒜_U`. Then for a.e. `u ∈ [0, 1]`,
`J^{u,λᵤ}_W(μ·, αᵤ) = sup_{β ∈ 𝒜₁} J^{u,λᵤ}_W(μ·, β)`, where `αᵤ(t, x) := α(t, u, x)`.

**Formalization Note** `J^{u,m}_W(μ·, β)` is the reward of the control `(t, u', x) ↦ β(t, x)`
with initial law `δᵤ × m` (p.21). Solutions are relations: the hypothesis gives one solution
`Sα` under `α` whose reward dominates every solution under every `β ∈ 𝒜_U`; the conclusion is
that, for a.e. `u`, every solution under `αᵤ` dominates every solution under every
`β ∈ 𝒜₁` (all solutions are unique in law). -/
theorem lemma_5_1 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (κ : Kernel ℝ (Fin d → ℝ)) [IsMarkovKernel κ]
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (hμ : IsUnifFlow D.T μ)
    (α : ℝ≥0 → ℝ → (Fin d → ℝ) → A) (hα : IsUControl α)
    (hopt : ∃ Sα : GSol D α (lamOf κ), ∀ β : ℝ≥0 → ℝ → (Fin d → ℝ) → A, IsUControl β →
      ∀ S : GSol D β (lamOf κ), S.payoff W μ ≤ Sα.payoff W μ) :
    ∀ᵐ u ∂lebUnit,
      ∀ S : GSol D (fun t _ x => α t u x) ((Measure.dirac u).prod (κ u)),
      ∀ β : ℝ≥0 → (Fin d → ℝ) → A, IsOneControl β →
      ∀ S' : GSol D (fun t _ x => β t x) ((Measure.dirac u).prod (κ u)),
        S'.payoff W μ ≤ S.payoff W μ := by sorry

end GraphonLabelGame
