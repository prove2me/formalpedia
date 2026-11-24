-- Prove2me | Theorems.Thm_GlobalTheory_ResidueExtension_exists_generator
-- name    : GlobalTheory.ResidueExtension.exists_generator
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:08.511691+00:00
-- url     : https://prove2.me/theorems/f7a01813-0e9d-4944-858f-4bb6619b6ce8
-- title:
--   Residue Extension: exists generator
-- statement:
--   The Residue Extension construction uses the exists generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L60-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L60-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]

theorem GlobalTheory.ResidueExtension.exists_generator (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) {π : O}
    (hπ : Irreducible π) :
    ∃ G : O[X], (G.Monic ∨ G = 0) ∧ G.eval₂ r a = 0 ∧
      ∀ f : O[X], f.eval₂ r a = 0 → ∃ g h, f = G * g + C π * h := by sorry
