-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_image_inter
-- name    : GroundTheory.Arith.SchemeCoh.image_inter
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:07.73072+00:00
-- url     : https://prove2.me/theorems/27592090-1883-4fe4-9111-6842b8aae861
-- title:
--   Scheme Coh: image inter
-- statement:
--   The Scheme Coh construction uses the image inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechSeparated.lean#L92-L108

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

theorem GroundTheory.Arith.SchemeCoh.image_inter {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {κ : Type w}
    (U : κ → Y.Opens) {n : ℕ} (i : Fin (n + 1) → κ) :
    g ''ᵁ inter (X := Y.toTopCat) U i = inter (X := X.toTopCat) (fun a => g ''ᵁ U a) i := by sorry
