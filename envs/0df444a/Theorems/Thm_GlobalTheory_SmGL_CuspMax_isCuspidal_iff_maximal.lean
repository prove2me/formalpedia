-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_CuspMax_isCuspidal_iff_maximal
-- name    : GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:19.370276+00:00
-- url     : https://prove2.me/theorems/f10b29e9-156a-4e64-b907-ffe9c1841ff8
-- title:
--   Cusp Max: is Cuspidal iff maximal
-- statement:
--   The Cusp Max construction uses the is Cuspidal iff maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L89-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L89-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by sorry
