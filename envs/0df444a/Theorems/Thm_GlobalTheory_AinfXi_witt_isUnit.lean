-- Prove2me | Theorems.Thm_GlobalTheory_AinfXi_witt_isUnit
-- name    : GlobalTheory.AinfXi.witt_isUnit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:51.552583+00:00
-- url     : https://prove2.me/theorems/b43613a9-d84f-41da-b7de-71cf0b4c8af7
-- title:
--   Ainf Xi: witt is Unit
-- statement:
--   The Ainf Xi construction uses the witt is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L46-L54

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]

theorem GlobalTheory.AinfXi.witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by sorry
