-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_basicOpen
-- name    : GroundTheory.Arith.SchemeCoh.inter_basicOpen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:28.882033+00:00
-- url     : https://prove2.me/theorems/5482681d-bc01-4f7e-bdbc-583cd4f249fb
-- title:
--   Scheme Coh: inter basic Open
-- statement:
--   The Scheme Coh construction uses the inter basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L54-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L54-L67

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.inter_basicOpen {V : X.Opens} {κ : Type u} (h : κ → Γ(X, V)) :
    ∀ {n : ℕ} (i : Fin (n + 1) → κ),
      inter (X := X.toTopCat) (fun a => X.basicOpen (h a)) i = X.basicOpen (∏ a, h (i a))
  := by sorry
