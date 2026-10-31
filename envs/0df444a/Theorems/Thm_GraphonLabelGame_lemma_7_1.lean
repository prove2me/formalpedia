-- Prove2me | Theorems.Thm_GraphonLabelGame_lemma_7_1
-- name    : GraphonLabelGame.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:25.083488+00:00
-- url     : https://prove2.me/theorems/16f67ceb-24dc-4f58-be47-cbc8a5f6f832
-- title:
--   Lemma 7.1 — $\sup_{\beta\in\mathcal A_n}\Delta^{n,i}_2(\beta,u^n)\le0$ for a.e. $u^n$
-- statement:
--   Assume the standing assumptions of §3. Let $W\in L^1_+[0,1]^2$, let $\mu_\cdot$ be a $W$-equilibrium with equilibrium control $\alpha^*$, and let $n\in\mathbb N$. For labels $u^n\in[0,1]^n$, let player $j$ use $\alpha^*(t,u^n_j,x_j)$ with $X^{n,j}_0\sim\lambda_{u^n_j}$ independently (7.1), and let $X^{n,\beta,u^n_i,i}$ be player $i$'s state when $i$ switches to $\beta\in\mathcal A_n$ (7.2). Define
--   $$\Delta^{n,i}_2(\beta,u^n)=\mathbb E\Big[\int_0^Tf(t,X^{n,\beta,u^n_i,i}_t,\mathsf W\mu_t(u^n_i),\beta_t)\,dt+g(X^{n,\beta,u^n_i,i}_T,\mathsf W\mu_T(u^n_i))\Big]-\mathbb E\Big[\int_0^Tf(t,X^{n,u^n_i,i}_t,\mathsf W\mu_t(u^n_i),\alpha^*(t,u^n_i,X^{n,u^n_i,i}_t))\,dt+g(X^{n,u^n_i,i}_T,\mathsf W\mu_T(u^n_i))\Big].$$
--   Then
--   $$\sup_{\beta\in\mathcal A_n}\Delta^{n,i}_2(\beta,u^n)\le0\qquad\text{for a.e. }u^n\in[0,1]^n\text{ and all }i\in[n].$$
--
--   With the true neighborhood measures replaced by their graphon limits, no player gains by deviating, even to a control that depends on all players' states.
--
--   Differences from the source:
--   - encoding: Δ^{n,i}_2(β, uⁿ), a difference of two expectations → delta2 evaluated on a solution S' of the deviated system (7.2) and a solution S of the undeviated system (7.1); the bound is claimed for all such pairs; reason: relation form; both systems are unique in law
--   - encoding: μ· is a W-equilibrium with equilibrium control α* (Definition 3.1) → IsWEquilibrium: α* ∈ 𝒜_U, μ· continuous P_Unif-valued, some solution S* under α* has L(U, X_t) = μ_t for t ∈ [0,T], and J_W(S) ≤ J_W(S*) for every α ∈ 𝒜_U and every solution S under α; reason: Definition 3.1 relation-wise; the ∃ S* form is no stronger than the paper's (solutions are unique in law)
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
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, Lemma 7.1, p.33 (Δ^{n,i}_2 defined on p.33; (7.1), (7.2) on p.32)

import Mathlib
import Definitions.Def_GraphonLabelGame_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **Lemma 7.1**. Lacker–Soret, arXiv:2204.09642v1, Lemma 7.1, p.33 (`Δ^{n,i}_2` defined on
p.33, the systems (7.1)–(7.2) on p.32). Under the standing assumptions, let `W ∈ L¹₊[0, 1]²`,
let `μ·` be a `W`-equilibrium with equilibrium control `α*` for the initial law
`λ = Unif[0, 1] ⊗ κ` (`κ` a version of `u ↦ λᵤ`), and let `n ∈ ℕ`. Then
`sup_{β ∈ 𝒜ₙ} Δ^{n,i}_2(β, uⁿ) ≤ 0` for a.e. `uⁿ ∈ [0, 1]ⁿ` and all `i ∈ [n]`.

**Formalization Note** `Δ^{n,i}_2` is evaluated on a solution `S'` of the system in which player
`i` uses `β` and the others use (3.8), and a solution `S` of the undeviated system (7.1);
the claim is for all such pairs. -/
theorem lemma_7_1 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (κ : Kernel ℝ (Fin d → ℝ)) [IsMarkovKernel κ]
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A)
    (heq : IsWEquilibrium D W (lamOf κ) μ αs) (n : ℕ) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin n => lebUnit), ∀ i : Fin n,
      ∀ β : ℝ≥0 → (Fin n → Fin d → ℝ) → A, IsNControl β →
      ∀ (S' : NSol D n (Function.update (labelProfile αs u) i β) κ u)
        (S : NSol D n (labelProfile αs u) κ u),
        delta2 W μ i S' S ≤ 0 := by sorry

end GraphonLabelGame
