-- Prove2me | Theorems.Thm_GlobalTheory_ArtinTransport_isFrob_comap
-- name    : GlobalTheory.ArtinTransport.isFrob_comap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:58:17.511693+00:00
-- url     : https://prove2.me/theorems/30482cd3-38e7-4545-a160-37bef4d32d08
-- title:
--   Artin Transport: is Frob comap
-- statement:
--   The Artin Transport construction uses the is Frob comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L42-L46

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FrobeniusRestrictScalarsPowModInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ArtinTransportAlgClosureEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
noncomputable section
open GlobalTheory GlobalTheory.ArtinTransport
open scoped Pointwise
variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
variable [NumberField E] [NumberField E'] (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') {σ : G E Ω} {τ : G E' Ω'}

theorem GlobalTheory.ArtinTransport.isFrob_comap (h : ∀ z, φ (σ z) = τ (φ z)) {q : ℕ} (hτ : IsFrob (F := E') A' q τ) :
    IsFrob (F := E) (A'.comap φ.toRingHom) q σ := by sorry
