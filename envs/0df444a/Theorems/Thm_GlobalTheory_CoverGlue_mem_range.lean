-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_mem_range
-- name    : GlobalTheory.CoverGlue.mem_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:59.696279+00:00
-- url     : https://prove2.me/theorems/44244d3c-ff77-4520-bd84-52010ba607b1
-- title:
--   Cover Glue: mem range
-- statement:
--   The Cover Glue construction uses the mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueHom.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueHom.lean#L43-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem GlobalTheory.CoverGlue.mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by sorry
