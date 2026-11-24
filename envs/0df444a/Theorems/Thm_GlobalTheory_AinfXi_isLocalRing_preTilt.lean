-- Prove2me | Theorems.Thm_GlobalTheory_AinfXi_isLocalRing_preTilt
-- name    : GlobalTheory.AinfXi.isLocalRing_preTilt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:39.044913+00:00
-- url     : https://prove2.me/theorems/9f3280b6-fb78-45b7-8384-cb5eeedaba57
-- title:
--   Ainf Xi: is Local Ring pre Tilt
-- statement:
--   The Ainf Xi construction uses the is Local Ring pre Tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L70-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open GlobalTheory GlobalTheory.AinfXi
open GlobalTheory.Sandwich
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem GlobalTheory.AinfXi.isLocalRing_preTilt (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by sorry
