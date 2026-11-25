-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualHermitianLatticesTorsionBlocks_cj_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks.cj_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:00.843075+00:00
-- url     : https://prove2.me/theorems/234bac5c-893c-44ab-a22d-5e219edb4bfe
-- title:
--   Self Dual Hermitian Lattices Torsion Blocks: cj mem
-- statement:
--   The Self Dual Hermitian Lattices Torsion Blocks construction uses the cj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/HermitianLattices.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/HermitianLattices.lean#L45-L47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks.cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by sorry
