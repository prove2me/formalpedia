-- Prove2me | Theorems.Thm_GlobalTheory_InfAdeleMixed_mixed_ext
-- name    : GlobalTheory.InfAdeleMixed.mixed_ext
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:36.601559+00:00
-- url     : https://prove2.me/theorems/2290c27d-d32a-50d9-a6f6-953b73d81ae0
-- title:
--   Inf Adele Mixed: mixed ext
-- statement:
--   The Inf Adele Mixed construction uses the mixed ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInfiniteAdeleTensorEquivMixedSpace.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInfiniteAdeleTensorEquivMixedSpace.lean#L20-L22

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

theorem GlobalTheory.InfAdeleMixed.mixed_ext [IsTotallyComplex E] {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y := by sorry
