-- Prove2me | Theorems.Thm_GroundTheory_Global_inner_toMixed_symm
-- name    : GroundTheory.Global.inner_toMixed_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:29.716735+00:00
-- url     : https://prove2.me/theorems/e175e692-917f-463f-b434-2607e1b13278
-- title:
--   Global: inner to Mixed symm
-- statement:
--   The Global construction uses the inner to Mixed symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L90-L94

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
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
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.inner_toMixed_symm (x y : mixedSpace K) :
    ⟪(euclidean.toMixed K).symm x, (euclidean.toMixed K).symm y⟫ =
      ∑ w, x.1 w * y.1 w + ∑ w, (conj (x.2 w) * y.2 w).re := by sorry
