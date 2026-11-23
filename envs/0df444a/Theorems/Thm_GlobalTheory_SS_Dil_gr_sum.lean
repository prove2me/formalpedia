-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_gr_sum
-- name    : GlobalTheory.SS.Dil.gr_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:04.284587+00:00
-- url     : https://prove2.me/theorems/da282d28-c6ab-4a33-81a7-31b97b3c691f
-- title:
--   Dil: gr sum
-- statement:
--   The Dil construction uses the gr sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L102-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
variable {R S : Type} {n : ℕ} [CommRing R] [CommRing S] (σ : MvPolynomial (Fin n) R →+* S)

theorem GlobalTheory.SS.Dil.gr_sum (f : Fin n → MvPolynomial (Fin n) R) : gr σ (∑ j, f j) = ∑ j, gr σ (f j) := by sorry
