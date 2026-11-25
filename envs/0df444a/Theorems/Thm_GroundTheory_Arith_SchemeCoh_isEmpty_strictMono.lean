-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isEmpty_strictMono
-- name    : GroundTheory.Arith.SchemeCoh.isEmpty_strictMono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:25.514836+00:00
-- url     : https://prove2.me/theorems/e8348bb4-1f3c-4d9a-8de0-d95dcdd31fcf
-- title:
--   Scheme Coh: is Empty strict Mono
-- statement:
--   The Scheme Coh construction uses the is Empty strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Ordered.lean#L339-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Ordered.lean#L339-L345

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Ordered
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
variable {X : TopCat.{u}} {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.isEmpty_strictMono [Finite ι] {n : ℕ} (hn : Nat.card ι ≤ n) :
    IsEmpty {i : Fin (n + 1) → ι // StrictMono i} := by sorry
