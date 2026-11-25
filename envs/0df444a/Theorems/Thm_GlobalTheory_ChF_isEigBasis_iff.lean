-- Prove2me | Theorems.Thm_GlobalTheory_ChF_isEigBasis_iff
-- name    : GlobalTheory.ChF.isEigBasis_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:20.619573+00:00
-- url     : https://prove2.me/theorems/64f85227-decd-5c6a-9af3-8236a20f0dfd
-- title:
--   Ch F: is Eig Basis iff
-- statement:
--   The Ch F construction uses the is Eig Basis iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/IsEigBasisIff.lean#L180-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/IsEigBasisIff.lean#L180-L181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF

theorem GlobalTheory.ChF.isEigBasis_iff {O OE : Type} [CommRing O] [CommRing OE] {d s : ℕ} (act : OE → Fin d → PS O 1 d)
    (τ : OE →+* O) (w : Fin s → Fin d → O) : IsEigBasis act τ w ↔ EigB (fun a => linPart (act a)) τ w := by sorry
