-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFieldExt_card_torsion
-- name    : GlobalTheory.TorsionFieldExt.card_torsion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:39.436481+00:00
-- url     : https://prove2.me/theorems/8fe1592f-60fe-4876-b090-31bb81261e56
-- title:
--   Torsion Field Ext: card torsion
-- statement:
--   The Torsion Field Ext construction uses the card torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionPointsFieldExtension.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionPointsFieldExtension.lean#L28-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointsFieldExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionFieldExt
variable {S : Scheme.{0}}

theorem GlobalTheory.TorsionFieldExt.card_torsion (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by sorry
