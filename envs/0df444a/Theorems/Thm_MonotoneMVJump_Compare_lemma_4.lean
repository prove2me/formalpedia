-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_lemma_4
-- name    : MonotoneMVJump.Compare.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:21.152767+00:00
-- url     : https://prove2.me/theorems/35866ed3-d0d5-46b9-ab9d-425bfc07e537
-- title:
--   Lemma 4 — the optimal MV wealth lies in the domain of monotonicity $\mathcal G_\theta$ iff Assumption 1 holds
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z=Z^{z,t}$, $\theta>0$, $x\in\mathbb R$, and $R$ solving (38) with $\mathbb E[R_T]\ne1$, $\mathrm{Var}[R_T]>0$. Then an admissible pair $(\pi^*,X^{\pi^*})$, $\pi^*\in\mathcal B_{x,z,t}$, following the optimal MV strategy (39) exists. For every such pair,
--   $$X^{\pi^*}_T\in\mathcal G_\theta=\Big\{f\in\mathcal L^2(\mathbb P):\ f-\mathbb E^{\mathbb P}[f]\le\frac1\theta\ \text{a.s.}\Big\}\iff\text{Assumption 1 holds at }(z,t).$$
--
--   MMV and MV preferences agree exactly on $\mathcal G_\theta$ (Maccheroni et al. 2009). So this lemma decides whether the MV optimum is also evaluated identically by MMV preferences.
--
--   **Formalization Note** The lemma's "Equation (1)" is read as (20)/(21), the equation whose solution Proposition 1 provides. $\mathbb E[R_T]\ne1$ and $\mathrm{Var}[R_T]>0$ make explicit the division in (39).
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 27, Lemma 4

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Lemma 4 (p. 27): a feedback pair `(π*, X^{π*})` of (39) exists and is admissible for the MV
problem, and for every such pair the terminal wealth `X^{π*}_T` lies in the domain of
monotonicity `𝒢_θ` if and only if Assumption 1 holds at `(z, t)`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (θ : ℝ) (hθ : 0 < θ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ) (hR : IsRProcess M G t Z R)
    (hER : ∫ ω, R M.T ω ∂M.P ≠ 1) (hVar : 0 < variance (R M.T) M.P) :
    (∃ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) ∧ M.AdmB t x Z π X) ∧
      ∀ π X : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T →
          π s ω = mvStrategy39 M G (Dstar M.P θ x R M.T) Z X s ω) → M.AdmB t x Z π X →
        (InDomMono M.P θ (X M.T) ↔ Assumption1 M G t Z) := by sorry

end MonotoneMVJump.Compare
