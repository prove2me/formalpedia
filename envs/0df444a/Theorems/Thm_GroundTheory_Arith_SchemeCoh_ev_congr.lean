-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_congr
-- name    : GroundTheory.Arith.SchemeCoh.ev_congr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:08.964922+00:00
-- url     : https://prove2.me/theorems/b99ca558-1e3d-4a6b-8e99-9a3293d4ba5a
-- title:
--   Scheme Coh: ev congr
-- statement:
--   The Scheme Coh construction uses the ev congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L182-L186

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable (A : X → AddCommGrpCat.{u})
variable {U}
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.ev_congr {n : ℕ} (σ : Cochain (discPresheaf A) U n) {j₁ j₂ : Fin (n + 1) → ι}
    (h : j₁ = j₂) (x : X) (h₁ : x ∈ inter U j₁) (h₂ : x ∈ inter U j₂) :
    ev A x h₁ (σ j₁) = ev A x h₂ (σ j₂) := by sorry
