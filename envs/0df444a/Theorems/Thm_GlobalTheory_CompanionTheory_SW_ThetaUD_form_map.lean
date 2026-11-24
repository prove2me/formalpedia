-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_form_map
-- name    : GlobalTheory.CompanionTheory.SW.ThetaUD.form_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:16.774108+00:00
-- url     : https://prove2.me/theorems/8e758be4-4eb6-4913-9146-5901115a86b0
-- title:
--   Theta UD: form map
-- statement:
--   The Theta UD construction uses the form map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L15-L20

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.ThetaUD.form_map {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by sorry
