-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_d
-- name    : GroundTheory.Arith.SchemeCoh.ev_d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:14.650772+00:00
-- url     : https://prove2.me/theorems/096828f6-bc3c-426c-a3a3-d3bb119a7030
-- title:
--   Scheme Coh: ev d
-- statement:
--   The Scheme Coh construction uses the ev d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L188-L194

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
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.ev_d {n : ℕ} (σ : Cochain (discPresheaf A) U n) (i : Fin (n + 2) → ι) (x : X)
    (hx : x ∈ inter U i) :
    ev A x hx (d (discPresheaf A) U n σ i) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      ev A x (inter_le_comp U i k.succAbove hx) (σ (i ∘ k.succAbove)) := by sorry
