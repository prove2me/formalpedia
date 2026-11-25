-- Prove2me | Theorems.Thm_GroundTheory_Global_prod_card_stabilizer_infinitePlace
-- name    : GroundTheory.Global.prod_card_stabilizer_infinitePlace
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:38.256595+00:00
-- url     : https://prove2.me/theorems/8f74ab4c-5ccb-58ac-b15d-5333a78f0430
-- title:
--   Global: prod card stabilizer infinite Place
-- statement:
--   The Global construction uses the prod card stabilizer infinite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L69-L80

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
omit [NumberField L]
open scoped Classical

theorem GroundTheory.Global.prod_card_stabilizer_infinitePlace
    [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L))] :
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L),
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by sorry
