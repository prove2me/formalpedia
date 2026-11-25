-- Prove2me | Theorems.Thm_GroundTheory_Brauer_degree_matrixCSA
-- name    : GroundTheory.Brauer.degree_matrixCSA
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:27.039401+00:00
-- url     : https://prove2.me/theorems/4fed407d-05a0-433f-85a2-94fc7f4d6553
-- title:
--   Brauer: degree matrix CSA
-- statement:
--   The Brauer construction uses the degree matrix CSA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean#L73-L77

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
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
open Module TensorProduct
universe u v w
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.degree_matrixCSA (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    degree K (matrixCSA A n) = n * degree K A := by sorry
