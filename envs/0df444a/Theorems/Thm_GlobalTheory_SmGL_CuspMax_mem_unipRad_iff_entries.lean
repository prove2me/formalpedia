-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_CuspMax_mem_unipRad_iff_entries
-- name    : GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:55.336455+00:00
-- url     : https://prove2.me/theorems/3e079a4b-aee7-4b3a-93af-337d320d9ea3
-- title:
--   Cusp Max: mem unip Rad iff entries
-- statement:
--   The Cusp Max construction uses the mem unip Rad iff entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubsingletonJacquetOfPerm.lean#L27-L47

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

theorem GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by sorry
