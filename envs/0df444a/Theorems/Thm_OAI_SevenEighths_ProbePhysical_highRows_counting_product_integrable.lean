-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_highRows_counting_product_integrable
-- name    : OAI.SevenEighths.ProbePhysical.highRows_counting_product_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:41.812268+00:00
-- url     : https://prove2.me/theorems/dafe0196-0f59-4ac2-98fa-d81c4e03a280
-- title:
--   Integrability of high-row values against counting times height measure
-- statement:
--   Let $\rho$ be a countable measurable space with measurable singletons and $e:\rho\to$`NonzeroFrequency` injective; $\eta$ a `HeckeFamily.Character`, $S$ a finite set of ideals, $C$ `CalibrationData`, $D$ an ideal, reals $\sigma>3/2$, $\upsilon>2$, $\xi>1$, and $T$ an integrable continuous function on `HeightSpace`. Then $(p_1,p_2)\mapsto$`highRowOnLines η S C D σ υ ξ (e p₁) p₂`$\cdot T(p_2)$ is integrable for the product of counting measure and `heightMeasure`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.highRows_counting_product_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/InitialRows.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ρ×HeightSpace=>highRowOnLines η S C D σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
