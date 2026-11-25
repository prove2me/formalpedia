-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_inv_lower
-- name    : GlobalTheory.DegCnt.RatNormal.exists_inv_lower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:15.06144+00:00
-- url     : https://prove2.me/theorems/e892a251-2d82-41e1-bf40-e058a91a2ba2
-- title:
--   Rat Normal: exists inv lower
-- statement:
--   The Rat Normal construction uses the exists inv lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L58-L76

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
omit [StarRing K]

theorem GlobalTheory.DegCnt.RatNormal.exists_inv_lower {j : ℕ} (A : Matrix (Fin j) (Fin j) K) (h0 : ∀ a b, a < b → A a b = 0)
    (h1 : ∀ a, A a a = 1) :
    ∃ M : Matrix (Fin j) (Fin j) K, M * A = 1 ∧ (∀ a b, a < b → M a b = 0) ∧ ∀ a, M a a = 1 := by sorry
