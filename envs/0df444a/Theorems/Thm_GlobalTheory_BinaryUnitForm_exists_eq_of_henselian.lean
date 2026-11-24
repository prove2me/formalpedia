-- Prove2me | Theorems.Thm_GlobalTheory_BinaryUnitForm_exists_eq_of_henselian
-- name    : GlobalTheory.BinaryUnitForm.exists_eq_of_henselian
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:06.175787+00:00
-- url     : https://prove2.me/theorems/a9097479-e1c3-4bae-b88e-0bf83a68c6c1
-- title:
--   Binary Unit Form: exists eq of henselian
-- statement:
--   The Binary Unit Form construction uses the exists eq of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegers.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegers.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField IsLocalRing
open GlobalTheory GlobalTheory.BinaryUnitForm

theorem GlobalTheory.BinaryUnitForm.exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by sorry
