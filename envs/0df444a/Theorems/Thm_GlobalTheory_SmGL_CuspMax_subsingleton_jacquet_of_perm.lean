-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_CuspMax_subsingleton_jacquet_of_perm
-- name    : GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:36.583184+00:00
-- url     : https://prove2.me/theorems/3a2a5182-f79a-47af-9381-88ba21cfa9e4
-- title:
--   Cusp Max: subsingleton jacquet of perm
-- statement:
--   The Cusp Max construction uses the subsingleton jacquet of perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L74-L87

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

theorem GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by sorry
