-- Prove2me | Theorems.Thm_MinimaxWass_DataDep_c1_deterministic
-- name    : MinimaxWass.DataDep.c1_deterministic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:03.787222+00:00
-- url     : https://prove2.me/theorems/0757e8fb-67dd-43ed-9b18-9a1529b18477
-- title:
--   Appendix C.1, p. 13 — deterministic comparison with the supremum deviation
-- statement:
--   Fix $p\ge1$, $\varrho>0$, a probability law $P$, a nonempty class $\mathcal F$ of upper semicontinuous losses with $0\le f\le M$, a sample $Z_1,\ldots,Z_n$ with $n\ge1$, and $f\in\mathcal F$. Let $X_\lambda=\sup_{g\in\mathcal F}(\mathbb E_P\varphi_{\lambda,g}-\mathbb E_{P_n}\varphi_{\lambda,g})$. Then
--
--   $$R_{\varrho,p}(P,f)\le\inf_{\lambda\ge0}\{\lambda\varrho^p+\mathbb E_{P_n}\varphi_{\lambda,f}+X_\lambda\}.$$
--
--   This is the first deterministic step of Appendix C.1, comparing the population local worst-case risk with its empirical dual expression.
--
--   **Formalization Note** The source prints equality with the first dual expression; this item records only its first-to-last inequality, for which weak duality suffices. The instance space is bounded and Polish. Nonemptiness of $\mathcal F$ prevents the real supremum defining $X_\lambda$ from taking Lean's empty-family default value. The printed minimum is encoded as an infimum.
-- source:
--   Lee & Raginsky, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, Appendix C.1, p. 13, first display

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-- Appendix C.1, p. 13, first display: the first-to-last inequality. -/
theorem c1_deterministic {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbounded : Bornology.IsBounded (Set.univ : Set 𝒵))
    (p ϱ M : ℝ) (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF : ℱ.Nonempty)
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hval : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (P : ProbabilityMeasure 𝒵) (n : ℕ) (hn : 0 < n)
    (ω : Fin n → 𝒵) (f : 𝒵 → ℝ) (hf : f ∈ ℱ) :
    localRisk p ϱ P f ≤
      ⨅ lam : Set.Ici (0 : ℝ),
        lam.1 * ϱ ^ p +
        (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam.1 f (ω i) +
        Xlam p lam.1 P ℱ ω := by sorry

end MinimaxWass.DataDep
