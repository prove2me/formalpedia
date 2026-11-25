-- Prove2me | Theorems.Thm_GlobalTheory_xClasses_denom
-- name    : GlobalTheory.xClasses_denom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:23.321014+00:00
-- url     : https://prove2.me/theorems/c01e8686-bae1-4dba-91a5-10b0df15fcea
-- title:
--   Global Theory: x Classes denom
-- statement:
--   The Global Theory construction uses the x Classes denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/XClassesDenom.lean#L50-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/XClassesDenom.lean#L50-L78

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_XClassesDenom
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
open GlobalTheory

theorem GlobalTheory.xClasses_denom {K : Type} [Field K] [NumberField K] (A : Ideal (𝓞 K)) {r : ℕ}
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (f : Fin r → Fin (r + 1))
    (S : Matrix (Fin r) (Fin r) K)
    (hx : ∀ a b, ∀ α ∈ A, ∃ o : 𝓞 K,
      (o : K) = (α : K) * (S * Y.map (algebraMap (𝓞 K) K)) a b) (i j : Fin r) :
    ∀ α ∈ Ideal.span {(Y.submatrix id f).det} * A, ∃ o : 𝓞 K, (o : K) = (α : K) * S i j := by sorry
