-- Prove2me | Theorems.Thm_GlobalTheory_IsoIdem_star_mul_comm
-- name    : GlobalTheory.IsoIdem.star_mul_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:33.450857+00:00
-- url     : https://prove2.me/theorems/bbc6c40e-0507-4316-9667-eaddb729e343
-- title:
--   Iso Idem: star mul comm
-- statement:
--   The Iso Idem construction uses the star mul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L36-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem

theorem GlobalTheory.IsoIdem.star_mul_comm {E : Type} [Field E] [StarRing E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hA : A.IsHermitian) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) :
    star y * A = A * star y := by sorry
