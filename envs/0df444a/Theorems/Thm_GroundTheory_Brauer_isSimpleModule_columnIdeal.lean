-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isSimpleModule_columnIdeal
-- name    : GroundTheory.Brauer.isSimpleModule_columnIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:10.13733+00:00
-- url     : https://prove2.me/theorems/789f5383-dc3e-4a83-b23c-68835fe65635
-- title:
--   Brauer: is Simple Module column Ideal
-- statement:
--   The Brauer construction uses the is Simple Module column Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L199-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L199-L227

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v w
variable {K : Type u} [Field K]
variable {R : Type v} [Ring R] [Algebra K R] {D : Type w} [DivisionRing D] [Algebra K D]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (e : R ≃ₐ[K] Matrix ι ι D) (i₀ : ι)

theorem GroundTheory.Brauer.isSimpleModule_columnIdeal : IsSimpleModule R (columnIdeal e i₀) := by sorry
