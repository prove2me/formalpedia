-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_theorem_2_4_ii
-- name    : ModelFreeBounds.Duality.theorem_2_4_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:31.830201+00:00
-- url     : https://prove2.me/theorems/2568bb06-452d-4df8-b402-bf46703f338b
-- title:
--   Theorem 2.4(ii), p. 6 — some y gives ϕ(f) + ⟨y, g⟩ − π(y) ≥ f; the infimum in (2.2) is attained when ϕ(f) < ∞
-- statement:
--   Let $\Omega$ be a nonempty Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$ satisfying the no-arbitrage Assumption 2.1. Let $f:\Omega\to\mathbb R$ be Borel measurable and let $\phi(f)$ be its superhedging price (2.2). Then:
--
--   1. there exists $y\in\mathbb R^m$ such that
--   $$\phi(f)+\langle y,g\rangle(\omega)-\pi(y)\ge f(\omega)\qquad\text{for every }\omega\in\Omega;$$
--   2. hence, if $\phi(f)<\infty$, the infimum in (2.2) is attained: there are $c\in\mathbb R$ and $y\in\mathbb R^m$ with $c+\langle y,g\rangle\ge f$ on $\Omega$ and $c+\pi(y)=\phi(f)$.
--
--   The existence of an optimal static hedge is the practical content of the duality: the model-free upper price bound is realised by an actual portfolio.
--
--   **Formalization Note** The inequality in part 1 is stated in `EReal`; when $\phi(f)=+\infty$ it holds trivially, as on the page. The hypothesis that $\Omega$ is nonempty is added, as in Theorem 2.4(i): for $\Omega=\emptyset$ one has $\phi(f)=-\infty<\infty$, and the infimum in (2.2) is not attained by any real $c+\pi(y)$, so part 2 would fail.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Theorem 2.4(ii), p. 6

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem theorem_2_4_ii {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [Nonempty Ω] {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) :
    (∃ y : Fin m → ℝ, ∀ ω,
      (f ω : EReal) ≤ M.superhedgingPrice f + ((M.pay y ω - M.cost y : ℝ) : EReal)) ∧
    (M.superhedgingPrice f < ⊤ → ∃ (c : ℝ) (y : Fin m → ℝ), (∀ ω, f ω ≤ c + M.pay y ω) ∧
      M.superhedgingPrice f = ((c + M.cost y : ℝ) : EReal)) := by sorry

end ModelFreeBounds.Duality
