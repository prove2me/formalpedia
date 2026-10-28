-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_HomogeneousAnalysis_Geometry_finite_stabilizer_harmonic_image_bs
-- name    : OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:31:52.748705+00:00
-- url     : https://prove2.me/theorems/d2c56346-4ccc-4134-a787-8ed35078b3c9
-- title:
--   OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image` of [lean/OAI/Probability/CriticalPercolation/Harmonic/GraphHarmonicLinear.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/GraphHarmonicLinear.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry`, with `open Set Function`, `open scoped Classical BigOperators`, `open HarmonicAnalysis`):
--
--   ```lean
--   lemma finite_stabilizer_harmonic_image_bs (d k : ℕ) (hg : W.HasDegree d) :
--       (Set.range (fun a : W.Stab => W.harmonicRepresentation k a.val)).Finite
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.Aut`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.HasDegree`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.Stab`, `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.harmonicRepresentation` and `OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.polynomialHarmonicSpace` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.RelativeGrowth.virtually_indicable_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Harmonic/GraphHarmonicLinear.lean (declaration OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.finite_stabilizer_harmonic_image)

import Mathlib
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma finite_stabilizer_harmonic_image_bs (d k : ℕ) (hg : W.HasDegree d) :
    (Set.range (fun a : W.Stab => W.harmonicRepresentation k a.val)).Finite := by
  sorry

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
end
