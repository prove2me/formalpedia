-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_chain
-- name    : GlobalTheory.SS.Dil.chain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:43.596379+00:00
-- url     : https://prove2.me/theorems/fb16d98c-fa92-4272-8b91-bb1f0abef725
-- title:
--   Dil: chain
-- statement:
--   The Dil construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L68-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L68-L85

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

theorem GlobalTheory.SS.Dil.chain {R S W : Type} {n : ℕ} [CommRing R] [CommRing S] [AddCommGroup W] [Module S W]
    (σ : MvPolynomial (Fin n) R →+* S) (D : MvPolynomial (Fin n) R → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = σ x • D y + σ y • D x) (hr : ∀ r, D (C r) = 0) (p : MvPolynomial (Fin n) R) :
    D p = ∑ i, σ (pderiv i p) • D (X i) := by sorry
