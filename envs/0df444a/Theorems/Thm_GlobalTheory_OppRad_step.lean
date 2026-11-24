-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_step
-- name    : GlobalTheory.OppRad.step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:02.337808+00:00
-- url     : https://prove2.me/theorems/0cdca971-e5c7-411c-8bb8-a04944cf062c
-- title:
--   Opp Rad: step
-- statement:
--   The Opp Rad construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L121-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L121-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}

theorem GlobalTheory.OppRad.step {a b c d : R} (aa : a * a = a) (bb : b * b = b) (cc : c * c = c) (dd : d * d = d)
    (ab : a * b = 0) (ac : a * c = 0) (ad : a * d = 0) (ba : b * a = 0) (bc : b * c = 0) (bd : b * d = 0)
    (ca : c * a = 0) (cb : c * b = 0) (cd : c * d = 0) (da : d * a = 0) (db : d * b = 0) (dc : d * c = 0)
    (h1 : OppInj π a c) (h2 : OppInj π (a + b) d) {v : V} (hv : ∀ u ∈ U (a + b) (c + d), π u v = v)
    (h0 : S π (U (c + d) (a + b)) v = 0) : S π (U (a + c) (b + d)) v = 0 := by sorry
