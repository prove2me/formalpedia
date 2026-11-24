-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pt_comp
-- name    : GlobalTheory.CompanionTheory.AxForm.pt_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:26:03.761807+00:00
-- url     : https://prove2.me/theorems/24cfef0c-f934-4be2-a9dd-6f57dc5e8afa
-- title:
--   Ax Form: pt comp
-- statement:
--   The Ax Form construction uses the pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L216-L221

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.AxForm.pt_comp {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] {ρ : R →+* C} {ρ' : R →+* C'}
    {ρ'' : R →+* C''} (f : C →+* C') (h : f.comp ρ = ρ') (g : C' →+* C'') (h' : g.comp ρ' = ρ'')
    (k : C →+* C'') (hk : g.comp f = k) (h'' : k.comp ρ = ρ'') : pt g h' ≫ pt f h = pt k h'' := by sorry
