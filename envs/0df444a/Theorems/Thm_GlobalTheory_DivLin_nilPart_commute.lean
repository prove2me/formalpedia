-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_nilPart_commute
-- name    : GlobalTheory.DivLin.nilPart_commute
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:53.578056+00:00
-- url     : https://prove2.me/theorems/857a9d18-d492-4666-839f-ce750f5ffa60
-- title:
--   Div Lin: nil Part commute
-- statement:
--   The Div Lin construction uses the nil Part commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L83-L89

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

theorem GlobalTheory.DivLin.nilPart_commute {M : I → Module.End O H} (f : Module.End O H) (hM : ∀ i, Commute (M i) f) (l : ℕ) (t : I → R) :
    Commute (nilPart l M R t) (f.baseChange R) := by sorry
