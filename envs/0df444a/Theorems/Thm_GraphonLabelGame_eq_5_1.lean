-- Prove2me | Theorems.Thm_GraphonLabelGame_eq_5_1
-- name    : GraphonLabelGame.eq_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:31.267188+00:00
-- url     : https://prove2.me/theorems/ed5ec8b6-cb6e-474c-b6fd-9dadc3f68436
-- title:
--   (5.1) — the frozen-label value: $\sup_{\beta\in\mathcal A_1}J^{u,m}_W(\mu_\cdot,\beta)=\sup_{P\in\mathcal R_{u,m}}\langle P,\Gamma^{\mu_\cdot}\rangle$
-- statement:
--   Assume the standing assumptions of §3. Let $W\in L^1_+[0,1]^2$ and $\mu_\cdot\in C([0,T];\mathcal P_{\mathrm{Unif}}([0,1]\times\mathbb R^d))$. For $u\in[0,1]$, $m\in\mathcal P(\mathbb R^d)$ and $\beta\in\mathcal A_1$ let $X^{m,\beta}$ solve $dX_t=b(t,X_t,\beta(t,X_t))\,dt+\sigma(t,X_t)\,dB_t$, $X_0\sim m$, and
--   $$J^{u,m}_W(\mu_\cdot,\beta)=\mathbb E\Big[\int_0^Tf(t,X^{m,\beta}_t,\mathsf W\mu_t(u),\beta(t,X^{m,\beta}_t))\,dt+g(X^{m,\beta}_T,\mathsf W\mu_T(u))\Big].$$
--   Let $\mathcal R_{u,m}$ be the set of laws $P$ on the canonical space with $P\circ(U,X_0)^{-1}=\delta_u\times m$ under which every $N^\varphi$, $\varphi\in C^\infty_c(\mathbb R^d)$, is a martingale. Then
--   $$\sup_{\beta\in\mathcal A_1}J^{u,m}_W(\mu_\cdot,\beta)=\sup_{P\in\mathcal R_{u,m}}\langle P,\Gamma^{\mu_\cdot}\rangle.\tag{5.1}$$
--
--   This is the frozen-label version of (4.10); it is what allows optimality of a control to be transferred from the label-randomized problem to almost every fixed label (Lemma 5.1) and to deviations depending on all players' states (Lemma 7.1).
--
--   Differences from the source:
--   - encoding: J^{u,m}_W(μ·, β) for X^{m,β} the unique in law solution with X₀ ∼ m (p.21) → the graphon-game reward of the control (t, u', x) ↦ β(t, x) with initial law δᵤ × m, on any solution; reason: U = u a.s., so the measure argument is 𝐖μₜ(u); solutions are unique in law
--   - encoding: the two suprema → suprema in EReal over controls and solutions, resp. over ℛ_{u,m}; reason: no junk value at an empty index set
--   - reading: "σ is Lipschitz" (p.6) → σ(t,·) Lipschitz in x with one constant for all t ∈ [0,T] (entrywise); reason: the weaker of the two readings, hence the stronger theorem; well-posedness via [49, Theorem 1] (pp.7–8) needs only this
--   - encoding: standing assumptions of §3 (p.6): b, σ, f, g bounded continuous on [0,T] × ⋯ → Data.Standing: ContinuousOn and bounded on Iic T × ⋯, M₊(ℝᵈ) = FiniteMeasure with the weak topology; reason: the functions are only used on [0,T]
--   - encoding: d, d₀ ∈ ℕ, T > 0 (p.6) → 1 ≤ d and 0 < T; d₀ ≥ 1 is not stated separately; reason: the paper's ℕ starts at 1; d₀ ≥ 1 follows from σσᵀ ≥ c·I with c > 0 and d ≥ 1
--   - encoding: "the unique solution" of the state SDE (pp.7–8, 21) → solutions are a relation (GSol / NSol: a filtered probability space with an F-Brownian motion and a continuous adapted state satisfying the Itô equation); statements quantify over all solutions; reason: under the standing assumptions solutions exist and are unique in law ([49] cited p.7), so every payoff equals the paper's
--   - encoding: a given filtered probability space (Ω, F, 𝔽, P) (p.8), B¹,…,Bⁿ independent Brownian motions (p.7) → any probability space with a filtration for which the Brownian motion(s) are adapted with increments independent of the past; filtration not augmented; Itô integrals in the sense of Peng1990.SMP.IsItoIntegral; reason: payoffs depend only on the law of the solution, which is unique in law
--   - encoding: time t ∈ [0,T], labels u ∈ [0,1], ℝᵈ, C^d = C([0,T];ℝᵈ) → time ℝ≥0 read on [0,T] (paths clamped at T), labels in ℝ, ℝᵈ = Fin d → ℝ (sup norm), C^d = C(Icc 0 T, Fin d → ℝ) with its Borel σ-field; reason: Lean conventions; only t ∈ [0,T] and u ∈ [0,1] enter, and the norms on ℝᵈ give the same topology
--   - encoding: measurable controls on [0,T] × [0,1] × ℝᵈ (𝒜_U), [0,T] × ℝᵈ (𝒜₁), [0,T] × (ℝᵈ)ⁿ (𝒜ₙ) → measurable maps on ℝ≥0 × ℝ × ℝᵈ, ℝ≥0 × ℝᵈ, ℝ≥0 × (ℝᵈ)ⁿ; reason: every control on the smaller domain extends measurably; values outside never enter
--   - encoding: 𝐖m(u) ∈ M₊(E) (2.6) → Wop W m u, set to 0 at the labels u where ∫W(u,v)m(dv,dx) = ∞; reason: for m with uniform first marginal these labels form a Lebesgue-null set (Fubini, p.15), which no expectation over a uniform label sees
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, proof of Lemma 5.1, (5.1), p.22 (J^{u,m}_W defined on p.21)

import Mathlib
import Definitions.Def_GraphonLabelGame_Relaxed

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **(5.1)**. Lacker–Soret, arXiv:2204.09642v1, proof of Lemma 5.1, (5.1), p.22 (with
`J^{u,m}_W` of p.21). Under the standing assumptions, for `W ∈ L¹₊[0, 1]²`, a measure flow
`μ· ∈ C([0, T]; P_Unif([0, 1] × ℝᵈ))`, `u ∈ [0, 1]` and `m ∈ P(ℝᵈ)`,
`sup_{β ∈ 𝒜₁} J^{u,m}_W(μ·, β) = sup_{P ∈ ℛ_{u,m}} ⟨P, Γ^{μ·}⟩`, where `ℛ_{u,m}` is the set of
`P ∈ P(Ω)` with `P ∘ (U, X₀)⁻¹ = δᵤ × m` under which every `N^φ` is a martingale.

**Formalization Note** `J^{u,m}_W(μ·, β)` is the graphon-game reward of the control
`(t, u', x) ↦ β(t, x)` with initial law `δᵤ × m` (so `U = u` a.s. and the measure argument is
`𝐖μₜ(u)`), on any solution of the state equation (they are unique in law). Suprema in
`EReal`. -/
theorem eq_5_1 {d d₀ : ℕ} {A : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A]
    (D : Data d d₀ A) (hD : D.Standing) (W : ℝ → ℝ → ℝ) (hW : IsKernelL1Plus W)
    (μ : ℝ≥0 → ProbabilityMeasure (ℝ × (Fin d → ℝ))) (hμ : IsUnifFlow D.T μ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (m : ProbabilityMeasure (Fin d → ℝ)) :
    (⨆ (β : ℝ≥0 → (Fin d → ℝ) → A) (_ : IsOneControl β)
        (S : GSol D (fun t _ x => β t x) ((Measure.dirac u).prod (m : Measure (Fin d → ℝ)))),
        ((S.payoff W μ : ℝ) : EReal)) =
      ⨆ (P : ProbabilityMeasure (CanSpace d D.T A))
        (_ : P ∈ admissibleLaws D ((Measure.dirac u).prod (m : Measure (Fin d → ℝ)))),
        ((∫ ω, Gamma D W μ ω ∂(P : Measure (CanSpace d D.T A)) : ℝ) : EReal) := by sorry

end GraphonLabelGame
