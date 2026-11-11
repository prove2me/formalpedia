-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_IsolatedIterationData_stage_move_s236
-- name    : OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:08:13.371175+00:00
-- url     : https://prove2.me/theorems/8e78d64d-47fa-43fa-9d37-11ebfd62546e
-- title:
--   OAI.HarmonicArtin.IsolatedIterationData.stage_move_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.IsolatedIterationData.stage_move` of [lean/OAI/Topology/ArtinGroups/Realizations/WeightedCounts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Realizations/WeightedCounts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.IsolatedIterationData`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open _root_.Matrix _root_.OAI.Matrix`, `open scoped BigOperators`):
--
--   ```lean
--   theorem stage_move_s236 (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
--       (j:D.J) (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
--       (hp:∀ k,k<t→D.openSocle z k)
--       (hs:∃ H L c,0 < classLayerSocleDimension Q t (.inl j,L) c (O z D.s H)) :
--       D.capped ((.inl j,true)::z) ∧
--       (∀ H,ClassLowerBound Q b (O ((.inl j,true)::z) D.s H)) ∧
--       (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
--       (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
--         classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.fusionQuiver` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass` (definitions bundle `OAIQ236Ap002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_diag`, `OAI.HarmonicArtin.coxeterFusionEdge_symm` and `OAI.HarmonicArtin.fusionLabelSize` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.fusionPacketOrbit`, `OAI.HarmonicArtin.fusionPacketPerm` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayer` (definitions bundle `OAIQ236Ap005` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassLowerBound` (definitions bundle `OAIQ236Ap006` of this split); `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.IsolatedIterationData.capped`, `OAI.HarmonicArtin.IsolatedIterationData.openSocle` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLayerSocleDimension` (definitions bundle `OAIQ236Ap008` of this split).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Realizations/WeightedCounts.lean (declaration OAI.HarmonicArtin.IsolatedIterationData.stage_move)

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
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {M:CoxeterMatrix S}
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "O" => fusionPacketOrbit m d hd hdiag
local notation "T" => fusionPacketPerm m d hd hdiag (K:=ℂ)

namespace IsolatedIterationData
variable (D:IsolatedIterationData M)

theorem stage_move_s236 (z:List ((S⊕Unit)×Bool)) (hz:D.valid z) (hc:D.capped z)
    (j:D.J) (b t:ℤ) (ht:t<D.q) (hb:∀ H,ClassLowerBound Q b (O z D.s H))
    (hp:∀ k,k<t→D.openSocle z k)
    (hs:∃ H L c,0 < classLayerSocleDimension Q t (.inl j,L) c (O z D.s H)) :
    D.capped ((.inl j,true)::z) ∧
    (∀ H,ClassLowerBound Q b (O ((.inl j,true)::z) D.s H)) ∧
    (∀ k,k<t→D.openSocle ((.inl j,true)::z) k) ∧
    (∀ H,classLayer Q t (O ((.inl j,true)::z) D.s H)=
      classLayer Q t (T (.inl j) (classLayer Q t (O z D.s H)))) := by
  sorry

end IsolatedIterationData
end HarmonicArtin

end OAI
end
