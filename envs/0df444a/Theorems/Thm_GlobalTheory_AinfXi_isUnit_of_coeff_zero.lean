-- Prove2me | Theorems.Thm_GlobalTheory_AinfXi_isUnit_of_coeff_zero
-- name    : GlobalTheory.AinfXi.isUnit_of_coeff_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:55.6778+00:00
-- url     : https://prove2.me/theorems/99fad730-f097-4529-a14d-13677e8ba7de
-- title:
--   Ainf Xi: is Unit of coeff zero
-- statement:
--   The Ainf Xi construction uses the is Unit of coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L23-L38

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
variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem GlobalTheory.AinfXi.isUnit_of_coeff_zero {x : PreTilt O p} (h : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by sorry
