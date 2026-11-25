-- Prove2me | Theorems.Thm_GlobalTheory_FrobRestrict_frob_restrict
-- name    : GlobalTheory.FrobRestrict.frob_restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:51.015802+00:00
-- url     : https://prove2.me/theorems/2161f4dd-8dba-45b9-a9d8-69e035eca38c
-- title:
--   Frob Restrict: frob restrict
-- statement:
--   The Frob Restrict construction uses the frob restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FrobeniusRestrictScalarsPowModInertia.lean#L43-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FrobeniusRestrictScalarsPowModInertia.lean#L43-L74

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.FrobRestrict
open scoped Pointwise
open NumberField IsDedekindDomain
open scoped Pointwise

theorem GlobalTheory.FrobRestrict.frob_restrict : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω,
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧
    (∀ ι ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A, ι.restrictScalars E ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∧
    ∀ (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (φ : _root_.Formalism.ConjugateSelfDual.G E Ω), _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV w) σ → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) φ →
    σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by sorry
