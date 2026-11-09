-- Prove2me | Theorems.Thm_OAI_SharpPlanar_tableResidual_apply_g
-- name    : OAI.SharpPlanar.tableResidual_apply_g
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-09T03:19:49.765948+00:00
-- url     : https://prove2.me/theorems/30f2e99f-6f70-4bff-9ed8-f4ee01afd6ce
-- title:
--   OAI.SharpPlanar.tableResidual_apply_g: intermediate lemma from OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpPlanar.tableResidual_apply` of [lean/OAI/Analysis/PlanarPacking/ResidualBase.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ResidualBase.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpPlanar`, with `open Numerical`):
--
--   ```lean
--   lemma tableResidual_apply_g (a : Bool) (n : Node) (d : Bool) :
--       tableResidual a (n,d)=
--         (if d then (tableD a n.val:ℝ) else (tableC a n.val:ℝ))-
--         transformedJets (tableData (!a)) (n,d)+
--         (if a=false ∧ n.val=1 ∧ d=true then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpPlanar.Node` and `OAI.SharpPlanar.residues` (definitions bundle `OAIQ098G000` of this split); `OAI.SharpPlanar.tableC` and `OAI.SharpPlanar.tableD` (definitions bundle `OAIQ098G015` of this split); `OAI.SharpPlanar.transformedJets` (definitions bundle `OAIQ098G016` of this split); `OAI.SharpPlanar.tableData` (definitions bundle `OAIQ098G1691` of this split); `OAI.SharpPlanar.tableResidual` (definitions bundle `OAIQ098G1696` of this split).
--
--   **Used by.** The proofs of `OAI.SharpPlanar.Residual12.bound0_1_g`, `OAI.SharpPlanar.Residual12.bound1_1_g`, `OAI.SharpPlanar.Residual13.bound0_1_g`, `OAI.SharpPlanar.Residual13.bound1_1_g`, `OAI.SharpPlanar.Residual24.bound0_1_g`, `OAI.SharpPlanar.Residual25.bound0_0_g`, `OAI.SharpPlanar.Residual25.bound0_1_g`, `OAI.SharpPlanar.Residual25.bound1_0_g`, `OAI.SharpPlanar.Residual25.bound1_1_g`, `OAI.SharpPlanar.Residual27.bound0_0_g`, `OAI.SharpPlanar.Residual27.bound1_0_g`, `OAI.SharpPlanar.Residual31.bound0_1_g`, `OAI.SharpPlanar.Residual31.bound1_1_g`, `OAI.SharpPlanar.Residual33.bound0_1_g`, `OAI.SharpPlanar.Residual36.bound0_1_g`, `OAI.SharpPlanar.Residual36.bound1_0_g`, `OAI.SharpPlanar.Residual36.bound1_1_g`, `OAI.SharpPlanar.Residual37.bound1_0_g`, `OAI.SharpPlanar.Residual39.bound1_0_g`, `OAI.SharpPlanar.Residual40.bound0_1_g`, `OAI.SharpPlanar.Residual40.bound1_1_g`, `OAI.SharpPlanar.Residual43.bound0_0_g`, `OAI.SharpPlanar.Residual45.bound0_0_g`, `OAI.SharpPlanar.Residual45.bound1_1_g`, `OAI.SharpPlanar.Residual48.bound1_0_g`, `OAI.SharpPlanar.Residual48.bound1_1_g`, `OAI.SharpPlanar.Residual49.bound0_1_g`, `OAI.SharpPlanar.Residual4.bound1_1_g`, `OAI.SharpPlanar.Residual51.bound0_0_g`, `OAI.SharpPlanar.Residual51.bound1_1_g`, `OAI.SharpPlanar.Residual52.bound1_0_g`, `OAI.SharpPlanar.Residual55.bound0_1_g`, `OAI.SharpPlanar.Residual55.bound1_0_g`, `OAI.SharpPlanar.Residual57.bound0_1_g`, `OAI.SharpPlanar.Residual60.bound0_0_g`, `OAI.SharpPlanar.Residual60.bound1_1_g`, `OAI.SharpPlanar.Residual61.bound1_0_g`, `OAI.SharpPlanar.Residual63.bound1_1_g`, `OAI.SharpPlanar.Residual67.bound1_0_g`, `OAI.SharpPlanar.Residual84.bound1_1_g`, `OAI.SharpPlanar.Residual85.bound0_0_g`, `OAI.SharpPlanar.Residual85.bound0_1_g`, `OAI.SharpPlanar.Residual85.bound1_0_g`, `OAI.SharpPlanar.Residual85.bound1_1_g`, `OAI.SharpPlanar.Residual87.bound0_0_g`, `OAI.SharpPlanar.Residual87.bound0_1_g`, `OAI.SharpPlanar.Residual87.bound1_1_g`, `OAI.SharpPlanar.Residual88.bound0_0_g`, `OAI.SharpPlanar.Residual88.bound0_1_g`, `OAI.SharpPlanar.Residual88.bound1_0_g`, `OAI.SharpPlanar.Residual88.bound1_1_g`, `OAI.SharpPlanar.Residual91.bound0_0_g`, `OAI.SharpPlanar.Residual91.bound1_1_g`, `OAI.SharpPlanar.Residual93.bound0_0_g`, `OAI.SharpPlanar.Residual93.bound0_1_g`, `OAI.SharpPlanar.Residual93.bound1_0_g`, `OAI.SharpPlanar.Residual93.bound1_1_g`, `OAI.SharpPlanar.Residual96.bound0_0_g`, `OAI.SharpPlanar.Residual96.bound0_1_g`, `OAI.SharpPlanar.Residual96.bound1_0_g`, `OAI.SharpPlanar.Residual96.bound1_1_g`, `OAI.SharpPlanar.Residual97.bound0_0_g`, `OAI.SharpPlanar.Residual97.bound0_1_g`, `OAI.SharpPlanar.Residual99.bound0_0_g`, `OAI.SharpPlanar.residual_finite_exterior_0_g` and `OAI.SharpPlanar.residual_finite_exterior_1_g` of this split import it.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ResidualBase.lean (declaration OAI.SharpPlanar.tableResidual_apply)

import Mathlib
import Definitions.Def_OAIQ098G1691
import Definitions.Def_OAIQ098G1696

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Numerical
lemma tableResidual_apply_g (a : Bool) (n : Node) (d : Bool) :
    tableResidual a (n,d)=
      (if d then (tableD a n.val:ℝ) else (tableC a n.val:ℝ))-
      transformedJets (tableData (!a)) (n,d)+
      (if a=false ∧ n.val=1 ∧ d=true then 1 else 0) := by
  sorry
end SharpPlanar

end OAI
end
