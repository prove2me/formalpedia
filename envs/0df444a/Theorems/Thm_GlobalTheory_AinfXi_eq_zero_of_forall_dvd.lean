-- Prove2me | Theorems.Thm_GlobalTheory_AinfXi_eq_zero_of_forall_dvd
-- name    : GlobalTheory.AinfXi.eq_zero_of_forall_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:58.129015+00:00
-- url     : https://prove2.me/theorems/4bfb80ca-8f5f-4cdb-9b1a-00689f299d8b
-- title:
--   Ainf Xi: eq zero of forall dvd
-- statement:
--   The Ainf Xi construction uses the eq zero of forall dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L132-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FontaineAinfLocalDomainXiAdicOrder.lean#L132-L147

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
variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε

theorem GlobalTheory.AinfXi.eq_zero_of_forall_dvd (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by sorry
