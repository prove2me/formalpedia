-- Prove2me | Theorems.Thm_GlobalTheory_TanBasisLocal_dual_ext
-- name    : GlobalTheory.TanBasisLocal.dual_ext
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:48.197499+00:00
-- url     : https://prove2.me/theorems/50e1e345-1a28-4601-b53a-036d2ac1c14b
-- title:
--   Tan Basis Local: dual ext
-- statement:
--   The Tan Basis Local construction uses the dual ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L15-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_GlobalTheory_SqZero_dual_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal

theorem GlobalTheory.TanBasisLocal.dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp (DualNumber S) ⟶ Y}
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') : w = w' := by sorry
