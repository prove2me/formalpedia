-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_dudley
-- name    : MinimaxWass.DataDep.c1_dudley
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:11.4058+00:00
-- url     : https://prove2.me/theorems/d964f640-06bb-44aa-947c-92e76ceb5afb
-- title:
--   Appendix C.1, p. 14 — expected deviation bounded by the entropy integral
-- statement:
--   Under Assumptions 1–2, for a nonempty loss class $\mathcal F$, $n\ge1$ independent observations from $P$, and every fixed $\lambda\ge0$, the supremum deviation $X_\lambda$ satisfies
--
--   $$\mathbb E X_\lambda\le\frac{24}{\sqrt n}\,\mathfrak C(\mathcal F).$$
--
--   The displayed estimate is the complexity bound that enters both high-probability inequalities of Theorem 1.
--
--   **Formalization Note** The instance space is bounded and Polish, $p\ge1$, and $\varrho>0$. The internal uniform covering number is used in $\mathfrak C$; its finiteness is required before converting the extended integral to a real number.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 14, Dudley display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 14, entropy-integral display. -/
theorem c1_dudley {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF : ℱ.Nonempty)
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hC : entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (∫ ω, Xlam p lam P ℱ ω ∂(sampleLaw n P)) ≤
      24 * (entropyIntegral ℱ).toReal / Real.sqrt n := by sorry

end MinimaxWass.DataDep
