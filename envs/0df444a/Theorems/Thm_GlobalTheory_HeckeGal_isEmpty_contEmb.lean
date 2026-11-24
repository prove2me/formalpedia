-- Prove2me | Theorems.Thm_GlobalTheory_HeckeGal_isEmpty_contEmb
-- name    : GlobalTheory.HeckeGal.isEmpty_contEmb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:52.112807+00:00
-- url     : https://prove2.me/theorems/254dd8d3-f865-4630-b70a-a0ca449ec1ab
-- title:
--   Hecke Gal: is Empty cont Emb
-- statement:
--   The Hecke Gal construction uses the is Empty cont Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L115-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean#L115-L146

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.HeckeGal.isEmpty_contEmb {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    IsEmpty {j : v.adicCompletion E →+* Qbar l // Continuous j} := by sorry
