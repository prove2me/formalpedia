-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_exists_lift
-- name    : GlobalTheory.SS.Dil.exists_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:14.456046+00:00
-- url     : https://prove2.me/theorems/67446509-4ddb-46f4-af6b-9654cc957fa1
-- title:
--   Dil: exists lift
-- statement:
--   The Dil construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L8-L29

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

theorem GlobalTheory.SS.Dil.exists_lift {R B S W : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    [AddCommGroup W] [Module S W] (D : B → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = algebraMap B S x • D y + algebraMap B S y • D x)
    (hr : ∀ r, D (algebraMap R B r) = 0) :
    ∃ l : S ⊗[B] (KaehlerDifferential R B) →ₗ[S] W, ∀ b, l (1 ⊗ₜ KaehlerDifferential.D R B b) = D b := by sorry
