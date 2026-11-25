-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleMixed_exists_place_over
-- name    : GlobalTheory.InfAdeleMixed.exists_place_over
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:21:15.714569+00:00
-- url     : https://prove2.me/theorems/6c9ffbcb-9d2d-4005-aaad-9be10536d9fc
-- title:
--   Inf Adele Mixed: exists place over
-- statement:
--   The Inf Adele Mixed construction uses the exists place over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInfiniteAdeleTensorEquivMixedSpace.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInfiniteAdeleTensorEquivMixedSpace.lean#L24-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInfiniteAdeleTensorEquivMixedSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.InfAdeleMixed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.InfAdeleMixed.exists_place_over [IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by sorry
