-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_span_d
-- name    : GlobalTheory.SS.Dil.span_d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:12.635658+00:00
-- url     : https://prove2.me/theorems/7da31da6-70b0-4132-a3ea-72df517e0c7b
-- title:
--   Dil: span d
-- statement:
--   The Dil construction uses the span d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L31-L50

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

theorem GlobalTheory.SS.Dil.span_d (R B S : Type) [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (Q : Submodule S (S ⊗[B] (KaehlerDifferential R B))) (h : ∀ b, (1 : S) ⊗ₜ[B] KaehlerDifferential.D R B b ∈ Q) :
    ∀ x, x ∈ Q := by sorry
