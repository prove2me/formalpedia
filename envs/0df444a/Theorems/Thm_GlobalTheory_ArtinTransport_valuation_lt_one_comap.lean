-- Prove2me | Theorems.Thm_GlobalTheory_ArtinTransport_valuation_lt_one_comap
-- name    : GlobalTheory.ArtinTransport.valuation_lt_one_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:19.972408+00:00
-- url     : https://prove2.me/theorems/c9e9614b-09a9-482d-aec5-4d168181d648
-- title:
--   Artin Transport: valuation lt one comap
-- statement:
--   The Artin Transport construction uses the valuation lt one comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L22-L26

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

theorem GlobalTheory.ArtinTransport.valuation_lt_one_comap (A' : ValuationSubring Ω') (φ : Ω ≃+* Ω') (y : Ω) :
    (A'.comap φ.toRingHom).valuation y < 1 ↔ A'.valuation (φ y) < 1 := by sorry
