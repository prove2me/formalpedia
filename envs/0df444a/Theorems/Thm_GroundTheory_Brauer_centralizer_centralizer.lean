-- Prove2me | Theorems.Thm_GroundTheory_Brauer_centralizer_centralizer
-- name    : GroundTheory.Brauer.centralizer_centralizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:45.083032+00:00
-- url     : https://prove2.me/theorems/11f1f570-772a-47f1-8386-2c9f59d05782
-- title:
--   Brauer: centralizer centralizer
-- statement:
--   The Brauer construction uses the centralizer centralizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L169-L181

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
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
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]

theorem GroundTheory.Brauer.centralizer_centralizer :
    Subalgebra.centralizer K (Subalgebra.centralizer K (B : Set A) : Set A) = B := by sorry
