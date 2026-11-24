-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_exists_etZ_of_jac_ne_zero
-- name    : GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:52:38.799771+00:00
-- url     : https://prove2.me/theorems/9d53e800-b095-484c-be8e-8e8eb2f524d4
-- title:
--   Key Ka: exists et Z of jac ne zero
-- statement:
--   The Key Ka construction uses the exists et Z of jac ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteOfIsClosedSingleton.lean#L71-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FiniteOfIsClosedSingleton.lean#L71-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteOfIsClosedSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory.TransvFin

theorem GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n), (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → jac x s z c ≠ 0) → ∃ (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by sorry
