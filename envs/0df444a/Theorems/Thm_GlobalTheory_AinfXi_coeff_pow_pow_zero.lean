-- Prove2me | Theorems.Thm_GlobalTheory_AinfXi_coeff_pow_pow_zero
-- name    : GlobalTheory.AinfXi.coeff_pow_pow_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:55.777052+00:00
-- url     : https://prove2.me/theorems/56c7a025-4b6a-4aef-8a00-9ed2d199d49f
-- title:
--   Ainf Xi: coeff pow pow zero
-- statement:
--   The Ainf Xi construction uses the coeff pow pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L17-L21

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

theorem GlobalTheory.AinfXi.coeff_pow_pow_zero (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by sorry
