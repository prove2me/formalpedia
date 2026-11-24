-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_restr_iso
-- name    : GlobalTheory.DivLin.restr_iso
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:16.50119+00:00
-- url     : https://prove2.me/theorems/1ff87f24-30a2-430e-80b9-f5b37ac79bee
-- title:
--   Div Lin: restr iso
-- statement:
--   The Div Lin construction uses the restr iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L55-L60

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

theorem GlobalTheory.DivLin.restr_iso {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : ∀ x y, B.baseChange K (N x) (N' y) = 0) (x y : H) :
    B (M x) (M' y) = 0 := by sorry
