-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_cap_move_s236
-- name    : OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:05:44.505302+00:00
-- url     : https://prove2.me/theorems/ae9adb87-e5a0-4fd3-b688-71ecbf649594
-- title:
--   OAI.HarmonicArtin.IsolatedIterationData.cap_move_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.IsolatedIterationData.cap_move` of [lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.IsolatedIterationData`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   lemma cap_move_s236 (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
--       (k:ℤ) (hk:k<D.q) (hp:D.openSocle z (k-1)) (j:D.J)
--       (hs:∃ H L c,0 < classLayerSocleDimension Q k (.inl j,L) c (O z D.s H)) :
--       D.capped ((.inl j,true)::z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.fusionQuiver` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_diag`, `OAI.HarmonicArtin.coxeterFusionEdge_symm` and `OAI.HarmonicArtin.fusionLabelSize` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.fusionPacketOrbit` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.IsolatedIterationData.capped`, `OAI.HarmonicArtin.IsolatedIterationData.openSocle` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension` (definitions bundle `OAIQ236Ap008` of this split).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/IsolatedIterationData.lean (declaration OAI.HarmonicArtin.IsolatedIterationData.cap_move)

import Mathlib
import Definitions.Def_OAIQ236Ap008

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "hm" => (fun e=>le_trans (by norm_num) (fusionLabelSize_ge_four M e))
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "Y" => fusionOrbitLayer m d hd hdiag
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

namespace IsolatedIterationData
variable {M} (D:IsolatedIterationData M)

lemma cap_move_s236 (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (k:ℤ) (hk:k<D.q) (hp:D.openSocle z (k-1)) (j:D.J)
    (hs:∃ H L c,0 < classLayerSocleDimension Q k (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) := by
  sorry

end IsolatedIterationData
end HarmonicArtin

end OAI
end
