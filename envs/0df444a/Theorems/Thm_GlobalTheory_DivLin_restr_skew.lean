-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_restr_skew
-- name    : GlobalTheory.DivLin.restr_skew
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:48.04189+00:00
-- url     : https://prove2.me/theorems/6bd65d20-71e8-4a2f-bfb0-31bd28bded54
-- title:
--   Div Lin: restr skew
-- statement:
--   The Div Lin construction uses the restr skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L47-L53

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
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]
variable [Module.Free O H]

theorem GlobalTheory.DivLin.restr_skew {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (h : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (x y : H) :
    B (M x) y + B x (M y) = 0 := by sorry
