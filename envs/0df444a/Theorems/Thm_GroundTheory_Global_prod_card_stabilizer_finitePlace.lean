-- Prove2me | Theorems.Thm_GroundTheory_Global_prod_card_stabilizer_finitePlace
-- name    : GroundTheory.Global.prod_card_stabilizer_finitePlace
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:53.471464+00:00
-- url     : https://prove2.me/theorems/78eadbb7-8057-541f-8028-766aac2c5a8d
-- title:
--   Global: prod card stabilizer finite Place
-- statement:
--   The Global construction uses the prod card stabilizer finite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L114-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L114-L156

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L)))

theorem GroundTheory.Global.prod_card_stabilizer_finitePlace (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := stableMulAction S hS
    ∀ [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S)],
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) S,
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ) := by sorry
