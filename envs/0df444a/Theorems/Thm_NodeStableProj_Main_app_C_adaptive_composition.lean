-- Prove2me | Theorems.Thm_NodeStableProj_Main_app_C_adaptive_composition
-- name    : NodeStableProj.Main.app_C_adaptive_composition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:08.668983+00:00
-- url     : https://prove2.me/theorems/9e05a977-da57-4da1-9dc3-cac6dff94f9e
-- title:
--   App. C — basic adaptive composition of two (ε, δ)-indistinguishable stages
-- statement:
--   Let $\mu,\mu'$ be probability laws of a first-stage release on a measurable space $A$ with $\mu\approx_{\varepsilon_1,\delta_1}\mu'$, and let $\kappa,\kappa'$ be Markov kernels from $A$ to $B$ (the second stage, run on the first-stage output) with $\kappa(a)\approx_{\varepsilon_2,\delta_2}\kappa'(a)$ for every $a\in A$, where $\delta_1,\delta_2\ge0$. Then the joint laws of the transcript $(a,b)$ satisfy
--   $$\mu\otimes\kappa\ \approx_{\varepsilon_1+\varepsilon_2,\ \delta_1+\delta_2}\ \mu'\otimes\kappa' .$$
--
--   Appendix C combines the size estimate and the padded projection with it ([DR14, Theorem 3.16 and Appendix B]).
--
--   Differences from the source:
--   - generalization: first stage the released size, second stage the padded projection (countable spaces) → arbitrary measurable spaces A, B and Markov kernels; reason: the App. C stages are a special case (discrete spaces, every map a kernel)
--   - encoding: privacy parameters (ε, δ) with δ ≥ 0 → hypotheses 0 ≤ δ₁, 0 ≤ δ₂; reason: δ is a nonnegative slack; excludes only meaningless negative δ
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 34 and p. 35, Appendix C ("standard adaptive composition theorem", [DR14, Theorem 3.16 and Appendix B])

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory ProbabilityTheory

namespace NodeStableProj.Main

/-- Appendix C, p. 34 (basic adaptive composition, [DR14, Theorem 3.16 and Appendix B]): if the
first-stage laws satisfy `μ ≈_{ε₁,δ₁} μ'` and for every first-stage output `a` the second-stage
laws satisfy `κ a ≈_{ε₂,δ₂} κ' a`, then the joint laws of the transcript satisfy
`μ ⊗ κ ≈_{ε₁+ε₂, δ₁+δ₂} μ' ⊗ κ'`. -/
theorem app_C_adaptive_composition {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ μ' : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (κ κ' : Kernel A B) [IsMarkovKernel κ] [IsMarkovKernel κ']
    (ε₁ δ₁ ε₂ δ₂ : ℝ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (h₁ : PFRelease.Indist μ μ' ε₁ δ₁) (h₂ : ∀ a, PFRelease.Indist (κ a) (κ' a) ε₂ δ₂) :
    PFRelease.Indist (μ ⊗ₘ κ) (μ' ⊗ₘ κ') (ε₁ + ε₂) (δ₁ + δ₂) := by sorry

end NodeStableProj.Main
