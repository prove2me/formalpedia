-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_borel_mul_integralGL
-- name    : GroundTheory.Automorphic.Iwasawa.borel_mul_integralGL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:37.420238+00:00
-- url     : https://prove2.me/theorems/9abab67f-22c2-481b-9fb6-e4ae537eab33
-- title:
--   Iwasawa: borel mul integral GL
-- statement:
--   The Iwasawa construction uses the borel mul integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L352-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L352-L356

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Iwasawa.borel_mul_integralGL :
    (borel F n : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) = Set.univ := by sorry
