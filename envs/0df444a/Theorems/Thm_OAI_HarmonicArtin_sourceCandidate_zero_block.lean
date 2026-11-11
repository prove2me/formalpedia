-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceCandidate_zero_block
-- name    : OAI.HarmonicArtin.sourceCandidate_zero_block
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:51:33.955657+00:00
-- url     : https://prove2.me/theorems/f8963b9c-eb5e-4ee8-a6a2-f0720c2bf5e1
-- title:
--   OAI.HarmonicArtin.sourceCandidate_zero_block: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceCandidate_zero_block` of [lean/OAI/Topology/ArtinGroups/Harmonic/CandidateBlockNonpos.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/CandidateBlockNonpos.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix`):
--
--   ```lean
--   theorem sourceCandidate_zero_block (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
--       (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
--       (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
--       p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀t∈T,t∉J→∀L H b l,
--         classLevelArray R (bw h (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.artinParabolic` and `OAI.HarmonicArtin.FusionEdge.multiplicity` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.ReversibleQuiver.ProbeArrow` and `OAI.HarmonicArtin.ReversibleQuiver.ProbeVertex` (definitions bundle `OAIQ225Ag001` of this split); `OAI.HarmonicArtin.fusionQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialClass` (definitions bundle `OAIQ225Ag002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm` and `OAI.HarmonicArtin.fusionLabelSize` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.classLevelArray` (definitions bundle `OAIQ225Ag005` of this split); `OAI.HarmonicArtin.ReversibleQuiver.probeQuiver` (definitions bundle `OAIQ225Ag006` of this split); `OAI.HarmonicArtin.SourceCappedCandidate` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.sourceProbeAction` (definitions bundle `OAIQ225Ag013` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.IsSpherical` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proofs of `OAI.HarmonicArtin.sourceEarlierLower_contractible`, `OAI.HarmonicArtin.sourcePositiveBlock_contractible` and `OAI.HarmonicArtin.sourceResidue_lower_weights_contractible` of this split import it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/CandidateBlockNonpos.lean (declaration OAI.HarmonicArtin.sourceCandidate_zero_block)

import Mathlib
import Definitions.Def_HarmonicArtin
import Definitions.Def_OAIQ225Ag013

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPartialOrderPositiveCellPoset _root_.OAI.HarmonicArtin.liftedPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "Q" => fusionQuiver m d (coxeterFusionEdge_symm M)
local notation "R" => probeQuiver Q
local notation "bw" => sourceProbeAction M (K:=ℂ)

theorem sourceCandidate_zero_block (T J J':Set S) (hT:IsSpherical M T) (z h:Artin M)
    (hh:h∈artinParabolic M T) (q:ℤ) (p p':S⊕Unit→ℝ)
    (X:SourceCappedCandidate M T J z q p) (Y:SourceCappedCandidate M T J' (h*z) q p') :
    p=p' ∧ J=J' ∧ ∀s∈T,s∉J→∀t∈T,t∉J→∀L H b l,
      classLevelArray R (bw h (initialClass R (.inr ((.inl s,L),b)))) (.inl (.inl t,H),l)=0 := by
  sorry

end HarmonicArtin

end OAI
end
