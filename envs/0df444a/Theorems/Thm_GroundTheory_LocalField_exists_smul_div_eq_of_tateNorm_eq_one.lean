-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_smul_div_eq_of_tateNorm_eq_one
-- name    : GroundTheory.LocalField.exists_smul_div_eq_of_tateNorm_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:42.267009+00:00
-- url     : https://prove2.me/theorems/7303ffd0-b742-43f7-ae4d-48ef73640f00
-- title:
--   Local Field: exists smul div eq of tate Norm eq one
-- statement:
--   The Local Field construction uses the exists smul div eq of tate Norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L62-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L62-L79

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_smul_div_eq_of_tateNorm_eq_one {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by sorry
