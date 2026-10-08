-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_lemma_B_1
-- name    : HighDimCLT.Hyperrect.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:58.814711+00:00
-- url     : https://prove2.me/theorems/329f2492-1a4f-4bcb-a729-9bf32b72038b
-- title:
--   Lemma B.1, pp. 2324–2325 — Chebyshev association inequalities (18)–(20) for nondecreasing φ₁, φ₂ ≥ 0
-- statement:
--   Let $\varphi_1, \varphi_2 : \mathbb R \to [0, \infty)$ be nondecreasing functions and let $\xi_1, \xi_2$ be independent real-valued random variables, and assume that all the expectations below exist and are finite. Then
--
--   $$\begin{aligned}
--   &(18)\quad \mathrm E[\varphi_1(\xi_1)]\,\mathrm E[\varphi_2(\xi_1)] \le \mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_1)],\\
--   &(19)\quad \mathrm E[\varphi_1(\xi_1)]\,\mathrm E[\varphi_2(\xi_2)] \le \mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_1)] + \mathrm E[\varphi_1(\xi_2)\varphi_2(\xi_2)],\\
--   &(20)\quad \mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_2)] \le \mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_1)] + \mathrm E[\varphi_1(\xi_2)\varphi_2(\xi_2)].
--   \end{aligned}$$
--
--   Inequality (18) is Chebyshev's association inequality; (19) and (20) are the two-variable variants used to control third-moment terms in the proof of Lemma 5.1.
--
--   **Formalization Note** "All the expectations exist and are finite" is rendered as integrability of $\varphi_1(\xi_1)$, $\varphi_2(\xi_1)$, $\varphi_2(\xi_2)$, $\varphi_1(\xi_1)\varphi_2(\xi_1)$, $\varphi_1(\xi_2)\varphi_2(\xi_2)$ and $\varphi_1(\xi_1)\varphi_2(\xi_2)$, the functions whose expectations appear in (18)–(20).
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), pp. 2324–2325, App. B, Lemma B.1, displays (18)–(20)

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

theorem lemma_B_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂)
    (hφ₁0 : ∀ x, 0 ≤ φ₁ x) (hφ₂0 : ∀ x, 0 ≤ φ₂ x)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁ : Measurable ξ₁) (hξ₂ : Measurable ξ₂) (hind : IndepFun ξ₁ ξ₂ P)
    (hi₁ : Integrable (fun ω => φ₁ (ξ₁ ω)) P)
    (hi₂ : Integrable (fun ω => φ₂ (ξ₁ ω)) P)
    (hi₃ : Integrable (fun ω => φ₂ (ξ₂ ω)) P)
    (hi₁₁ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω)) P)
    (hi₂₂ : Integrable (fun ω => φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω)) P)
    (hi₁₂ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω)) P) :
    (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₁ ω) ∂P) ≤ ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P ∧
    (∫ ω, φ₁ (ξ₁ ω) ∂P) * (∫ ω, φ₂ (ξ₂ ω) ∂P) ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P ∧
    ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P := by sorry

end HighDimCLT.Hyperrect
