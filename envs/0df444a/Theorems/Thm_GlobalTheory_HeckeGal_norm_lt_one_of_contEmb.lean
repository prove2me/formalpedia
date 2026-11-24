-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_norm_lt_one_of_contEmb
-- name    : GlobalTheory.HeckeGal.norm_lt_one_of_contEmb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:03:09.869079+00:00
-- url     : https://prove2.me/theorems/ceb4483a-7ec2-40f2-9f79-89250d2f57f4
-- title:
--   Hecke Gal: norm lt one of cont Emb
-- statement:
--   The Hecke Gal construction uses the norm lt one of cont Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PlaceEqOfContEmbCompEq.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PlaceEqOfContEmbCompEq.lean#L9-L30

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PlaceEqOfContEmbCompEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.HeckeGal
open NumberField IsDedekindDomain

theorem GlobalTheory.HeckeGal.norm_lt_one_of_contEmb {E : Type} [Field E] [NumberField E]
    {l : ℕ} [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (hj : Continuous j)
    (a : 𝓞 E) (ha : a ∈ v.asIdeal) :
    ‖j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a))‖ < 1 := by sorry
