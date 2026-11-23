-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_nilPart_eq
-- name    : GlobalTheory.DivLin.nilPart_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:11.585456+00:00
-- url     : https://prove2.me/theorems/bb2829da-583c-4e69-9d86-220d24b1972a
-- title:
--   Div Lin: nil Part eq
-- statement:
--   The Div Lin construction uses the nil Part eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L73-L74

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

theorem GlobalTheory.DivLin.nilPart_eq (l : ℕ) (M : I → Module.End O H) (t : I → R) :
    nilPart l M R t = (lPrime l : R) • ∑ i, t i • (M i).baseChange R := by sorry
