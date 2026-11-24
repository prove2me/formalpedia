-- Prove2me | Theorems.Thm_GlobalTheory_PlaceCompletion_exists_initial_completion
-- name    : GlobalTheory.PlaceCompletion.exists_initial_completion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:18.985041+00:00
-- url     : https://prove2.me/theorems/4763797a-5a9e-4988-9636-b8de44254def
-- title:
--   Place Completion: exists initial completion
-- statement:
--   The Place Completion construction uses the exists initial completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAlgebraMapEqOfValVLeOne.lean#L281-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAlgebraMapEqOfValVLeOne.lean#L281-L349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero

theorem GlobalTheory.PlaceCompletion.exists_initial_completion :
    ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)), ∃ (T₀ : CDVR) (io₀ : K →+* T₀.Fr), OverLa la T₀.V io₀ 1 ∧ T₀.FinRes ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr), IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧ ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e := by sorry
