-- Prove2me | Theorems.Thm_GlobalTheory_DefinitePacking_absNorm_map_equiv
-- name    : GlobalTheory.DefinitePacking.absNorm_map_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:16:55.468161+00:00
-- url     : https://prove2.me/theorems/d9d2e80c-3c88-4226-8a2c-37136964a6ee
-- title:
--   Definite Packing: abs Norm map equiv
-- statement:
--   The Definite Packing construction uses the abs Norm map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OneLeNormMulAbsNormSq.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OneLeNormMulAbsNormSq.lean#L108-L111

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OneLeNormMulAbsNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.DefinitePacking

theorem GlobalTheory.DefinitePacking.absNorm_map_equiv {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.map (e : 𝓞 K →+* 𝓞 K)) = Ideal.absNorm I := by sorry
