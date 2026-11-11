-- Prove2me | Theorems.Thm_OAI_CKSSchwarzschild_numerical_equality
-- name    : OAI.CKSSchwarzschild.numerical_equality
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:50:09.497267+00:00
-- url     : https://prove2.me/theorems/b8963598-75f1-40d4-af85-40842e040766
-- title:
--   OAI.CKSSchwarzschild.numerical_equality: intermediate lemma from OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CKSMain.schwarzschild_equality_examples`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Area-controlled end replacement and the Bondi Penrose inequality in the CKS class*, OpenAI Math Release, September 27, 2026, result family 260, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CKSSchwarzschild.numerical_equality` of [lean/OAI/Geometry/Relativity/CKS/SchwarzschildCharges.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildCharges.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CKSSchwarzschild`, with `open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics`, `open scoped ContDiff Topology`, `open CKSBoundarySurface`):
--
--   ```lean
--   lemma numerical_equality {m : ℝ} (hm : 0 < m) :
--       Real.sqrt ((bondiCharge (cksData hm).massAspect).1^2 -
--         ‖(bondiCharge (cksData hm).massAspect).2‖^2) =
--       Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CKSSchwarzschild.smoothMetric` (definitions bundle `Q227CKS000` of this split); `OAI.CKSSchwarzschild.cksData` (definitions bundle `Q227CKS002` of this split); `OAI.CKSBoundarySurface.E3`, `OAI.CKSLorentz.E`, `OAI.CKSLorentz.bondiCharge`, `OAI.CKSSchwarzschild.Exterior`, `OAI.CKSSchwarzschild.Radial`, `OAI.CKSSchwarzschild.Sphere`, `OAI.CKSSchwarzschild.exteriorChartedSpace`, `OAI.CKSSchwarzschild.exteriorIsManifold`, `OAI.CKSSchwarzschild.tensorInner`, `OAI.CKSSourceExterior.minimumEnclosingArea` and `OAI.CKSSourceExterior.CKSData` (the published bundle `Def_CKSBondiPenrose`).
--
--   **Used by.** The proof of `OAI.CKSMain.schwarzschild_equality_examples` of this split imports it.
-- source:
--   OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 260; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildCharges.lean (declaration OAI.CKSSchwarzschild.numerical_equality)

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_Q227CKS002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma numerical_equality {m : ℝ} (hm : 0 < m) :
    Real.sqrt ((bondiCharge (cksData hm).massAspect).1^2 -
      ‖(bondiCharge (cksData hm).massAspect).2‖^2) =
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi)) := by
  sorry
end CKSSchwarzschild

end

end OAI
end
