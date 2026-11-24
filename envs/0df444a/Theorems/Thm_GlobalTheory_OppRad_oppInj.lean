-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_oppInj
-- name    : GlobalTheory.OppRad.oppInj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:25.803819+00:00
-- url     : https://prove2.me/theorems/0711185c-d299-4f6f-b717-a9f7eee45bc3
-- title:
--   Opp Rad: opp Inj
-- statement:
--   The Opp Rad construction uses the opp Inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L191-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L191-L250

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

theorem GlobalTheory.OppRad.oppInj (hreg : ∀ x : R, ∃ y, x * y * x = x) {p q : R} (pp : p * p = p) (qq : q * q = q)
    (pq : p * q = 0) (qp : q * p = 0) : OppInj π p q := by sorry
