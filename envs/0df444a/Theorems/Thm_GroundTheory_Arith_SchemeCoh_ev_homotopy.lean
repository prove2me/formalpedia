-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_homotopy
-- name    : GroundTheory.Arith.SchemeCoh.ev_homotopy
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:27:38.022534+00:00
-- url     : https://prove2.me/theorems/d316ba81-4258-4846-9d48-dde0cfc8dff0
-- title:
--   Scheme Coh: ev homotopy
-- statement:
--   The Scheme Coh construction uses the ev homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L236-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L236-L239

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

theorem GroundTheory.Arith.SchemeCoh.ev_homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) (j : Fin (n + 1) → ι)
    (x : X) (hx : x ∈ inter U j) :
    ev A x hx (homotopy U A σ j) = ev A x (mem_inter_cons U j hx)
      (σ (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j)) := by sorry
