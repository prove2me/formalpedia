-- Prove2me | Theorems.Thm_GlobalTheory_PowSec_exists_basis_of_isField
-- name    : GlobalTheory.PowSec.exists_basis_of_isField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:52:55.276645+00:00
-- url     : https://prove2.me/theorems/418085fd-52d7-463f-bc38-e458bc8d6dcf
-- title:
--   Pow Sec: exists basis of is Field
-- statement:
--   The Pow Sec construction uses the exists basis of is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsBasisOfIsField.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsBasisOfIsField.lean#L73-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsBasisOfIsField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec

theorem GlobalTheory.PowSec.exists_basis_of_isField {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (hR : IsField R)
    {m : ℕ} (hm : 0 < m) (h : Module.finrank R M = m) : Nonempty (Module.Basis (Fin m) R M) := by sorry
