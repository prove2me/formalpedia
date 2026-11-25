-- Prove2me | Theorems.Thm_GlobalTheory_HeightOneHopf_exists_isPtDer_dual
-- name    : GlobalTheory.HeightOneHopf.exists_isPtDer_dual
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:16:31.465498+00:00
-- url     : https://prove2.me/theorems/39687ab6-25c8-4366-bfd5-d2561f7e84ed
-- title:
--   Height One Hopf: exists is Pt Der dual
-- statement:
--   The Height One Hopf construction uses the exists is Pt Der dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L25-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L25-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf

theorem GlobalTheory.HeightOneHopf.exists_isPtDer_dual {k H : Type*} [Field k] [CommRing H] [Bialgebra k H] {d : ℕ}
    (x : Fin d → H) (hx : ∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H))
    (hind : ∀ l : Fin d → k,
      ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) :
    ∃ δ : Fin d → H →ₗ[k] k, (∀ i, IsPtDer (δ i)) ∧
      ∀ i j, δ i (x j) = if i = j then 1 else 0 := by sorry
