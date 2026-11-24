-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow
-- name    : GroundTheory.Automorphic.Iwasawa.coe_torusPow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:08.874083+00:00
-- url     : https://prove2.me/theorems/317f363b-ff45-49a6-92e5-7a6f4d2378c3
-- title:
--   Iwasawa: coe torus Pow
-- statement:
--   The Iwasawa construction uses the coe torus Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L185-L188

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

theorem GroundTheory.Automorphic.Iwasawa.coe_torusPow (l : Fin n → ℤ) :
    ((torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => (GLnLocal.uniformizer F : F) ^ l i := by sorry
