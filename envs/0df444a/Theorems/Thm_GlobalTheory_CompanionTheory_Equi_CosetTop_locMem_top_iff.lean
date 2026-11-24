-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetTop_locMem_top_iff
-- name    : GlobalTheory.CompanionTheory.Equi.CosetTop.locMem_top_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:41.880795+00:00
-- url     : https://prove2.me/theorems/a7955ee0-2f4d-457f-8435-ecf59dcc4323
-- title:
--   Coset Top: loc Mem top iff
-- statement:
--   The Coset Top construction uses the loc Mem top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetUnitIdealIntegral.lean#L19-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetUnitIdealIntegral.lean#L19-L45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.Equi.CosetTop.locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by sorry
