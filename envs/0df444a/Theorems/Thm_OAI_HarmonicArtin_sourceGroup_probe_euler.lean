-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_sourceGroup_probe_euler
-- name    : OAI.HarmonicArtin.sourceGroup_probe_euler
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:50:59.973639+00:00
-- url     : https://prove2.me/theorems/46d194d0-754e-4189-a227-a36a1f905b37
-- title:
--   OAI.HarmonicArtin.sourceGroup_probe_euler: intermediate lemma from OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.sourceGroup_probe_euler` of [lean/OAI/Topology/ArtinGroups/Harmonic/GroupProbeEuler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/GroupProbeEuler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`, `open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric`):
--
--   ```lean
--   theorem sourceGroup_probe_euler
--       (J T:Set S) (hJ:IsSpherical M J) (z g:Artin M) (hg:g∈artinParabolic M T)
--       (q:ℤ) (p:S⊕Unit→ℝ)
--       (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
--         (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
--       (hp:∀j:J,(C *ᵥ p) (.inl (j:S))=0)
--       (hext:∀v,v∉Sum.inl '' J→sourceMultiplicity M z q v=p v)
--       (huniv:∀a∈artinParabolic M J,
--         (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
--           (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
--         ∀j:J,p (.inl (j:S))≤ sourceMultiplicity M (a*z) q (.inl (j:S)))
--       (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
--       (hsoc:∀j:J,∀L c,coefficientSocle R
--         ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
--           (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
--       let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
--         (minimalClassModel_minimal R _) l);
--       (if l=0 then fusionWeight m α.2*p α.1 else 0)-
--         (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
--         fusionWeight m α.2*sourceMultiplicity M (g*z) (q-l) α.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FusionLabel`, `OAI.HarmonicArtin.FusionQuiverArrow`, `OAI.HarmonicArtin.FusionVertex`, `OAI.HarmonicArtin.StringLabel`, `OAI.HarmonicArtin.artinParabolic`, `OAI.HarmonicArtin.fusionWeight`, `OAI.HarmonicArtin.FusionEdge.multiplicity`, `OAI.HarmonicArtin.GeneratorPlacement.level` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex` (definitions bundle `OAIQ225Ag000` of this split); `OAI.HarmonicArtin.ReversibleQuiver.ProbeArrow` and `OAI.HarmonicArtin.ReversibleQuiver.ProbeVertex` (definitions bundle `OAIQ225Ag001` of this split); `OAI.HarmonicArtin.fusionQuiver`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.initialClass`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.FiniteModel` (definitions bundle `OAIQ225Ag002` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionFold`, `OAI.HarmonicArtin.fusionFoldedCartan`, `OAI.HarmonicArtin.fusionLabelSize` and `OAI.HarmonicArtin.unfoldedInclusion` (definitions bundle `OAIQ225Ag003` of this split); `OAI.HarmonicArtin.ReversibleQuiver.closedNeighborhood`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.ClassCapOn`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.generatorVector`, `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.minimalClassModel_minimal` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.pureLayer` (definitions bundle `OAIQ225Ag005` of this split); `OAI.HarmonicArtin.ReversibleQuiver.probeQuiver` and `OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.coefficientSocle` (definitions bundle `OAIQ225Ag006` of this split); `OAI.HarmonicArtin.sourceFrameFamily` and `OAI.HarmonicArtin.sourceMultiplicity` (definitions bundle `OAIQ225Ag011` of this split); `OAI.HarmonicArtin.sourceProbeAction` (definitions bundle `OAIQ225Ag013` of this split); `OAI.HarmonicArtin.Artin`, `OAI.HarmonicArtin.IsSpherical` and `OAI.HarmonicArtin.braidRelators` (the published bundle `Def_HarmonicArtin`).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.sourceCandidate_zero_block` of this split imports it.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/Harmonic/GroupProbeEuler.lean (declaration OAI.HarmonicArtin.sourceGroup_probe_euler)

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
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix _root_.OAI.Matrix CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "R" => probeQuiver Q
local notation "aw" => sourceArtinAction M (K:=ℂ)
local notation "bw" => sourceProbeAction M (K:=ℂ)
local notation "C" => fusionFoldedCartan m d

theorem sourceGroup_probe_euler
    (J T:Set S) (hJ:IsSpherical M J) (z g:Artin M) (hg:g∈artinParabolic M T)
    (q:ℤ) (p:S⊕Unit→ℝ)
    (hz:∀H,ClassCapOn Q (sourceFrameFamily M z H)
      (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)
    (hp:∀j:J,(C *ᵥ p) (.inl (j:S))=0)
    (hext:∀v,v∉Sum.inl '' J→sourceMultiplicity M z q v=p v)
    (huniv:∀a∈artinParabolic M J,
      (∀H,ClassCapOn Q (sourceFrameFamily M (a*z) H)
        (closedNeighborhood Q (Set.range (unfoldedInclusion M J))) q)→
      ∀j:J,p (.inl (j:S))≤ sourceMultiplicity M (a*z) q (.inl (j:S)))
    (α:FusionVertex (V:=S⊕Unit) m) (b:Bool) (l:ℤ)
    (hsoc:∀j:J,∀L c,coefficientSocle R
      ((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
        (minimalClassModel_minimal R _) l) (.inl (.inl (j:S),L)) c=⊥) :
    let N:=((minimalClassModel R (bw g⁻¹ (initialClass R (.inr (α,b))))).complex.pureLayer R
      (minimalClassModel_minimal R _) l);
    (if l=0 then fusionWeight m α.2*p α.1 else 0)-
      (fun β=>generatorVector R N (.inl β)) ⬝ᵥ fusionFold m (C *ᵥ p) ≤
      fusionWeight m α.2*sourceMultiplicity M (g*z) (q-l) α.1 := by
  sorry

end HarmonicArtin

end OAI
end
