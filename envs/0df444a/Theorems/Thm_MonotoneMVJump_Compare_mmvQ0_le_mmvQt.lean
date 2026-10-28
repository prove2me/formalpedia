-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_mmvQ0_le_mmvQt
-- name    : MonotoneMVJump.Compare.mmvQ0_le_mmvQt
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:50:55.167811+00:00
-- url     : https://prove2.me/theorems/8a77fc4e-8ca0-48be-874d-f3706917ccc6
-- title:
--   $V^0_\theta\le V^{\mathcal Q^t}_\theta$: MMV over $\mathcal Q_0$ lies below MMV over the Doléans-Dade measures
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be the probability space of the market, $t\ge0$, $\theta\in\mathbb R$ and $X:\Omega\to\mathbb R$. Write $V^{\mathcal Q^t}_\theta(X)$ for the MMV utility in which the infimum runs over the Doléans-Dade measures $\mathbb Q^{\eta,\phi}$, $(\eta,\phi)\in\mathcal M^t$ (density $\mathcal E_T\ge0$ with $\mathbb E[\mathcal E_T]=1$, $\mathbb E[\mathcal E_T^2]<\infty$), and $V^0_\theta(X)$ for the MMV utility in which it runs over all of $\mathcal Q_0=\{\mathbb Q\ll\mathbb P\text{ probability}:\mathbb E^{\mathbb P}[(d\mathbb Q/d\mathbb P)^2]<\infty\}$. Then
--   $$V^0_\theta(X)\le V^{\mathcal Q^t}_\theta(X).$$
--
--   Every Doléans-Dade measure of $\mathcal Q^t$ belongs to $\mathcal Q_0$ and gives the same value of the penalised expectation, so the infimum over the larger set is smaller. This is the right half of the chain $V_{MV}\le V^0_{MMV}\le V_{MMV}$ in the proof of Theorem 9.
--
--   **Formalization Note** Both sides are infima in the extended reals (`Market.mmvQ0`, `Market.mmvQt`); $\mathbb P$ is assumed to be a probability measure.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 28, proof of Theorem 9 ("for any admissible π, V_MV(X^π_T) ≤ V^0_MMV(X^π_T) ≤ V_MMV(X^π_T)" and the strict inequality (43)); Maccheroni, Marinacci, Rustichini & Taboga, Portfolio selection with monotone mean-variance preferences, Math. Finance 19 (2009), domain of monotonicity G_θ

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Proof of Theorem 9 (p. 28): since `𝒬^t ⊆ 𝒬₀`, the MMV preference over `𝒬₀` lies below the
MMV preference over the Doléans-Dade measures `𝒬^t`: `V⁰_θ(X) ≤ V^{𝒬^t}_θ(X)`. -/
theorem mmvQ0_le_mmvQt {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (hP : IsProbabilityMeasure M.P) (t : ℝ≥0) (θ : ℝ) (X : Ω → ℝ) :
    M.mmvQ0 θ X ≤ M.mmvQt t θ X := by sorry

end MonotoneMVJump.Compare
