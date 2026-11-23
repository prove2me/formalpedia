-- Prove2me | Theorems.Thm_GlobalTheory_FrobRestrict_isFrob_pow
-- name    : GlobalTheory.FrobRestrict.isFrob_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:38.266966+00:00
-- url     : https://prove2.me/theorems/48b917ba-563d-4941-98c8-b5097f79cbd5
-- title:
--   Frob Restrict: is Frob pow
-- statement:
--   The Frob Restrict construction uses the is Frob pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FrobeniusRestrictScalarsPowModInertia.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FrobeniusRestrictScalarsPowModInertia.lean#L14-L30

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

theorem GlobalTheory.FrobRestrict.isFrob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by sorry
