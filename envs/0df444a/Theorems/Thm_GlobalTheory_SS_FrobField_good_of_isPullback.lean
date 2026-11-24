-- Prove2me | Theorems.Thm_GlobalTheory_SS_FrobField_good_of_isPullback
-- name    : GlobalTheory.SS.FrobField.good_of_isPullback
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:34:02.111974+00:00
-- url     : https://prove2.me/theorems/cc300dff-4bcd-45cb-8918-c27869e6b016
-- title:
--   Frob Field: good of is Pullback
-- statement:
--   The Frob Field construction uses the good of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L210-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean#L210-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField

theorem GlobalTheory.SS.FrobField.good_of_isPullback {X G S T : Scheme.{0}} [IsAffine S] [IsAffine T] {g : X ⟶ G} {s : X ⟶ T}
    {a : G ⟶ S} {b : T ⟶ S} (H : IsPullback g s a b) (p r : ℕ) (hp : p.Prime) (hc : (p : Γ(X, ⊤)) = 0)
    (hT : ∀ c : Γ(T, ⊤), ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) (F : End X)
    (hg : (show X ⟶ X from F) ≫ g = absFrob X p r hp hc ≫ g) (hs : (show X ⟶ X from F) ≫ s = s)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (f : Γ(X, U)) : Good F (p ^ r) U f := by sorry
