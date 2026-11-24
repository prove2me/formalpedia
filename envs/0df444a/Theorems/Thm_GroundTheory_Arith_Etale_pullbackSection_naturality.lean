-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_pullbackSection_naturality
-- name    : GroundTheory.Arith.Etale.pullbackSection_naturality
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:31.260474+00:00
-- url     : https://prove2.me/theorems/165bc5bb-18d5-448f-b17a-0f1af824c0a6
-- title:
--   Etale: pullback Section naturality
-- statement:
--   The Etale construction uses the pullback Section naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ModulesPullback.lean#L20-L27

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

theorem GroundTheory.Arith.Etale.pullbackSection_naturality (g : T ⟶ U) {N N' : U.Modules} (φ : N ⟶ N') (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackSection g N n) =
      pullbackSection g N' (φ.app ⊤ n) := by sorry
