-- Prove2me | Theorems.Thm_GlobalTheory_ArtinTransport_isPlaceOver_comap
-- name    : GlobalTheory.ArtinTransport.isPlaceOver_comap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:57:58.232895+00:00
-- url     : https://prove2.me/theorems/64b2a9ba-feaa-4553-b177-50aede01e543
-- title:
--   Artin Transport: is Place Over comap
-- statement:
--   The Artin Transport construction uses the is Place Over comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L66-L73

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
variable {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω'] [Algebra E E']

theorem GlobalTheory.ArtinTransport.isPlaceOver_comap [NumberField E] [NumberField E'] (φ : Ω ≃+* Ω')
    (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) {A' : ValuationSubring Ω'}
    (hA : IsPlaceOver A' w) : IsPlaceOver (A'.comap φ.toRingHom) v := by sorry
