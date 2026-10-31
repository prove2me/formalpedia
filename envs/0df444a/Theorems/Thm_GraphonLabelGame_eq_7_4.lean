-- Prove2me | Theorems.Thm_GraphonLabelGame_eq_7_4
-- name    : GraphonLabelGame.eq_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:29.086882+00:00
-- url     : https://prove2.me/theorems/76f54da8-bbd1-4a4e-8df2-9ee475bcbf83
-- title:
--   (7.4) — the averaged error is bounded by the empirical-measure errors $\Delta^{n,i}_1$ and $\Delta^{n,i}_3$
-- statement:
--   Assume the standing assumptions of §3. Let $W\in L^1_+[0,1]^2$, let $\mu_\cdot$ be a $W$-equilibrium with equilibrium control $\alpha^*$, and let $\xi^n$ be an $n\times n$ matrix with nonnegative entries and zero diagonal. With $\Delta^{n,i}_1$ and $\Delta^{n,i}_3$ as on p.33 (player $i$'s reward with the true neighborhood measure $M^{n,u^n,i}_t$ minus the reward with the limiting $\mathsf W\mu_t(u^n_i)$, under a deviation $\beta$, resp. under $\alpha^*$, and the reverse difference for $\Delta^{n,i}_3$), for a.e. $u^n\in[0,1]^n$,
--   $$\frac1n\sum_{i=1}^n\epsilon^n_i(u^n)\le\frac1n\sum_{i=1}^n\sup_{\beta\in\mathcal A_n}\Delta^{n,i}_1(\beta,u^n)+\frac1n\sum_{i=1}^n\Delta^{n,i}_3(u^n).\tag{7.4}$$
--
--   Once the optimality of $\alpha^*$ has been used (Lemma 7.1), the averaged error is controlled by the discrepancy between neighborhood empirical measures and their graphon limits.
--
--   Differences from the source:
--   - reading: (7.4), printed without a quantifier on uⁿ → for a.e. uⁿ ∈ [0,1]ⁿ; reason: (7.4) averages the bound εⁿᵢ(uⁿ) ≤ sup_β Δ₁ + Δ₃ stated "a.e. uⁿ" on p.33
--   - encoding: Δ^{n,i}_1(β, uⁿ), Δ^{n,i}_3(uⁿ) → for every solution S of the undeviated system: sup over β ∈ 𝒜ₙ and solutions S' of the deviated system of delta1(S'), and delta3(S); inequality in EReal; reason: relation form; Δ^{n,i}_3 does not depend on the solution since the system is unique in law
--   - reading: "an arbitrary n×n matrix ξⁿ with positive entries and zeros on the diagonal" (§3.4, p.10) → IsInteractionMatrix: ξⁿᵢⱼ ≥ 0 and ξⁿᵢᵢ = 0; reason: positive entries contradict a zero diagonal; §3.1 (p.7) says nonnegative entries
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
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, (7.4), p.34 (Δ^{n,i}_1, Δ^{n,i}_3 defined on p.33)

import Mathlib
import Definitions.Def_GraphonLabelGame_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **(7.4)**. Lacker–Soret, arXiv:2204.09642v1, (7.4), p.34 (`Δ^{n,i}_1, Δ^{n,i}_3` defined on
p.33). Under the standing assumptions, let `W ∈ L¹₊[0, 1]²`, let `μ·` be a `W`-equilibrium
with equilibrium control `α*` for `λ = Unif[0, 1] ⊗ κ`, and let `ξⁿ` be an `n × n` matrix with
nonnegative entries and zero diagonal. Then for a.e. `uⁿ ∈ [0, 1]ⁿ`,
`(1/n) Σᵢ εⁿᵢ(uⁿ) ≤ (1/n) Σᵢ sup_{β ∈ 𝒜ₙ} Δ^{n,i}_1(β, uⁿ) + (1/n) Σᵢ Δ^{n,i}_3(uⁿ)`.

**Formalization Note** Stated in `EReal`. For a.e. `uⁿ` and every solution `S` of the
undeviated system (7.1): the supremum of `Δ^{n,i}_1` runs over `β ∈ 𝒜ₙ` and over solutions of
the deviated system (7.2), and `Δ^{n,i}_3` is computed on `S` (the paper's `Δ^{n,i}_3(uⁿ)` does not
depend on the solution, which is unique in law). -/
theorem eq_7_4 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (κ : Kernel ℝ (Fin d → ℝ)) [IsMarkovKernel κ]
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (αs : ℝ≥0 → ℝ → (Fin d → ℝ) → A)
    (heq : IsWEquilibrium D W (lamOf κ) μ αs) (n : ℕ)
    (ξ : Matrix (Fin n) (Fin n) ℝ) (hξ : IsInteractionMatrix ξ) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin n => lebUnit),
      ∀ S : NSol D n (labelProfile αs u) κ u,
        (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i, ((eps D ξ αs κ u i : ℝ≥0∞) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i,
              (⨆ (β : ℝ≥0 → (Fin n → Fin d → ℝ) → A) (_ : IsNControl β)
                (S' : NSol D n (Function.update (labelProfile αs u) i β) κ u),
                ((delta1 W μ ξ i S' : ℝ) : EReal))
            + (((n : ℝ)⁻¹ : ℝ) : EReal) * ∑ i, ((delta3 W μ ξ i S : ℝ) : EReal) := by sorry

end GraphonLabelGame
