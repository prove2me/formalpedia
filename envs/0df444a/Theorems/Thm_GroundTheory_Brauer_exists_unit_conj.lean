-- Prove2me | Theorems.Thm_GroundTheory_Brauer_exists_unit_conj
-- name    : GroundTheory.Brauer.exists_unit_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:02.225462+00:00
-- url     : https://prove2.me/theorems/02b31d29-7268-43d0-bf39-931d15833f68
-- title:
--   Brauer: exists unit conj
-- statement:
--   The Brauer construction uses the exists unit conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L126-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L126-L143

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
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
open SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  [IsSimpleRing B] [FiniteDimensional K B]

theorem GroundTheory.Brauer.exists_unit_conj (f g : B →ₐ[K] A) :
    ∃ a : Aˣ, ∀ x, g x = a * f x * ↑a⁻¹ := by sorry
