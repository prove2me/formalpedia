-- Prove2me | Theorems.Thm_OAI_CKSSchwarzschild_radial_round_vacuum
-- name    : OAI.CKSSchwarzschild.radial_round_vacuum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:49:49.535584+00:00
-- url     : https://prove2.me/theorems/50233e4b-9160-4069-8d7f-575ae61ae013
-- title:
--   OAI.CKSSchwarzschild.radial_round_vacuum: intermediate lemma from OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CKSMain.schwarzschild_equality_examples`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Area-controlled end replacement and the Bondi Penrose inequality in the CKS class*, OpenAI Math Release, September 27, 2026, result family 260, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CKSSchwarzschild.radial_round_vacuum` of [lean/OAI/Geometry/Relativity/CKS/SchwarzschildVacuumRound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildVacuumRound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CKSSchwarzschild`, with `open Set Filter CKSLorentz CKSCalculus CKSRound CKSRealizedRound CKSAngularGeometry`, `open scoped ContDiff Topology`):
--
--   ```lean
--   lemma radial_round_vacuum {m : ℝ} {v : ℝ → ℝ} {x : PhysicalPoint}
--       (hv : ContDiffAt ℝ ∞ v (x 0)) (hr : x 0 ≠ 0)
--       (hs : Real.sin (x 1) ≠ 0) (hp : 0 < CKSRealizedRound.radicand (fun _ => m) v x) :
--       let g := metricJet (CKSRealizedRound.lapse (fun _ => m) v) x
--       let k := tensorJet (CKSRealizedRound.lapse (fun _ => m) v) v
--         (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
--       g.energy k = 0 ∧ g.momentum k = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CKSRealizedRound.lapse`, `OAI.CKSRealizedRound.radial` and `OAI.CKSRealizedRound.radicand` (definitions bundle `Q227CKS001` of this split); `OAI.CKSRealizedRound.metricJet` and `OAI.CKSRealizedRound.tensorJet` (definitions bundle `Q227CKS002` of this split); `OAI.CKSAngularGeometry.PhysicalPoint`, `OAI.CKSRealizedRound.Point`, `OAI.CKSRound.Idx`, `OAI.CKSRound.MetricJet`, `OAI.CKSRound.TensorJet`, `OAI.CKSRound.MetricJet.energy` and `OAI.CKSRound.MetricJet.momentum` (the published bundle `Def_CKSBondiPenrose`).
--
--   **Used by.** The proofs of `OAI.CKSSchwarzschild.physical_DEC` and `OAI_CKSSchwarzschild_spherical_vacuum_regular` of this split import it.
-- source:
--   OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 260; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildVacuumRound.lean (declaration OAI.CKSSchwarzschild.radial_round_vacuum)

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
open Set Filter CKSLorentz CKSCalculus CKSRound CKSRealizedRound CKSAngularGeometry
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma radial_round_vacuum {m : ℝ} {v : ℝ → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ v (x 0)) (hr : x 0 ≠ 0)
    (hs : Real.sin (x 1) ≠ 0) (hp : 0 < CKSRealizedRound.radicand (fun _ => m) v x) :
    let g := metricJet (CKSRealizedRound.lapse (fun _ => m) v) x
    let k := tensorJet (CKSRealizedRound.lapse (fun _ => m) v) v
      (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
    g.energy k = 0 ∧ g.momentum k = 0 := by
  sorry
end CKSSchwarzschild

end

end OAI
end
