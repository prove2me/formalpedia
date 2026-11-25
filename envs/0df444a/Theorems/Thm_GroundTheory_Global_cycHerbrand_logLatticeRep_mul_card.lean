-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_logLatticeRep_mul_card
-- name    : GroundTheory.Global.cycHerbrand_logLatticeRep_mul_card
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:50:04.862028+00:00
-- url     : https://prove2.me/theorems/be104859-15f2-41ed-974b-9fae737217d9
-- title:
--   Global: cyc Herbrand log Lattice Rep mul card
-- statement:
--   The Global construction uses the cyc Herbrand log Lattice Rep mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L73-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L73-L129

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.cycHerbrand_logLatticeRep_mul_card {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (logLatticeRep K L) σ * Fintype.card (L ≃ₐ[K] L) =
      cycHerbrand (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by sorry
