-- Prove2me | Theorems.Thm_GlobalTheory_ArtinTransport_normV_eq_pow
-- name    : GlobalTheory.ArtinTransport.normV_eq_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:58:14.764451+00:00
-- url     : https://prove2.me/theorems/f3ab4c9d-a00e-4da1-812e-3d475dde927f
-- title:
--   Artin Transport: norm V eq pow
-- statement:
--   The Artin Transport construction uses the norm V eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ArtinTransportAlgClosureEquiv.lean#L75-L80

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

theorem GlobalTheory.ArtinTransport.normV_eq_pow [NumberField E] [NumberField E'] {v : HeightOneSpectrum (𝓞 E)} {w : HeightOneSpectrum (𝓞 E')}
    (hwv : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v.asIdeal) :
    normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by sorry
