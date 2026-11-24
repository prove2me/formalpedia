-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_nilPart_sq
-- name    : GlobalTheory.DivLin.nilPart_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:53.064234+00:00
-- url     : https://prove2.me/theorems/4a165bc3-7a20-452a-9302-1dfcb69b6951
-- title:
--   Div Lin: nil Part sq
-- statement:
--   The Div Lin construction uses the nil Part sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L76-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem GlobalTheory.DivLin.nilPart_sq {M : I → Module.End O H} (hMM : ∀ i j, M i * M j = 0) (l : ℕ) (t : I → R) :
    nilPart l M R t * nilPart l M R t = 0 := by sorry
