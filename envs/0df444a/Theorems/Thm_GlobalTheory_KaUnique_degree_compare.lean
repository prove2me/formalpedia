-- Prove2me | Theorems.Thm_GlobalTheory_KaUnique_degree_compare
-- name    : GlobalTheory.KaUnique.degree_compare
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:48:10.038303+00:00
-- url     : https://prove2.me/theorems/82aafb52-f1de-4613-afa1-de7cd716ff68
-- title:
--   Ka Unique: degree compare
-- statement:
--   The Ka Unique construction uses the degree compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KeyInvariantFromIntersectionUnique.lean#L55-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KeyInvariantFromIntersectionUnique.lean#L55-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonEqMulDetPowOfBasisChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KeyInvariantFromIntersectionUnique
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
noncomputable section
open GlobalTheory GlobalTheory.KaUnique

theorem GlobalTheory.KaUnique.degree_compare (hL : Out.Laws) {K : Type} [Field K] [CharZero K] (x : KeyIn K) {n l d : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hl : x.P.g * n < l)
    {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x} {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch')
    (σ : Equiv.Perm (Fin d)) (ga : Fin d → Kˣ)
    (hga : ∀ a (r : RR x (l - 0 * n)), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ (l - 0 * n) * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))))
    {b b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {t t' : Kˣ} {lam lam' : ℕ → Kˣ}
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j))
    (hb' : ∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b' j) (lam' j))
    (ht : KosVal x l s z ch b t) (ht' : KosVal x l s z' ch' b' t') :
    ∃ be : ℕ → Kˣ, t' = t * (∏ a, ga a) ^ (-2 * (l : ℤ)) * 1 ^ 2 *
        ∏ j ∈ Finset.range (x.P.g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (x.P.g.choose j : ℤ)) ∧
      ∀ j ≤ x.P.g, lam' j = lam j * be j ^ (-8 * ((l - j * n) ^ (3 * x.P.g + 2) : ℕ) : ℤ) *
        1 ^ (8 * (l - j * n) ^ (4 * x.P.g + 2)) := by sorry
