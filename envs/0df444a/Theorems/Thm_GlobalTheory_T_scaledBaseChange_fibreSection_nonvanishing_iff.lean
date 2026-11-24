-- Prove2me | Theorems.Thm_GlobalTheory_T_scaledBaseChange_fibreSection_nonvanishing_iff
-- name    : GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:39.008318+00:00
-- url     : https://prove2.me/theorems/3433aa0d-82e1-4aab-84b2-52b001b71f46
-- title:
--   T: scaled Base Change fibre Section nonvanishing iff
-- statement:
--   The T construction uses the scaled Base Change fibre Section nonvanishing iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionNonvanishingIffStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ScaledBaseChangeFibreSectionNonvanishingIffStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionNonvanishingIffStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by sorry
