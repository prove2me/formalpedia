-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_pullbackSection_smul
-- name    : GroundTheory.Arith.Etale.pullbackSection_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:36.949179+00:00
-- url     : https://prove2.me/theorems/6ec94dd5-fda5-431c-9dd2-2afd100a14b9
-- title:
--   Etale: pullback Section smul
-- statement:
--   The Etale construction uses the pullback Section smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {T U W : Scheme.{u}}

theorem GroundTheory.Arith.Etale.pullbackSection_smul (g : T ⟶ U) (N : U.Modules) (a : Γ(U, ⊤)) (n : Γ(N, ⊤)) :
    pullbackSection g N (a • n) = g.appTop a • pullbackSection g N n := by sorry
