-- Prove2me | Theorems.Thm_GroundTheory_Brauer_exists_isGalois_splits
-- name    : GroundTheory.Brauer.exists_isGalois_splits
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:32.358125+00:00
-- url     : https://prove2.me/theorems/cc11ed90-a9cd-557f-8e37-81c3d3cb4a9d
-- title:
--   Brauer: exists is Galois splits
-- statement:
--   The Brauer construction uses the exists is Galois splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L362-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L362-L381

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
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
open TensorProduct Module
universe u v w
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.exists_isGalois_splits (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by sorry
