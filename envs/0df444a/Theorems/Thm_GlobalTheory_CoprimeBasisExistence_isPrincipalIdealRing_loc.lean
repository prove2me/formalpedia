-- Prove2me | Theorems.Thm_GlobalTheory_CoprimeBasisExistence_isPrincipalIdealRing_loc
-- name    : GlobalTheory.CoprimeBasisExistence.isPrincipalIdealRing_loc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:18.358892+00:00
-- url     : https://prove2.me/theorems/07620148-4e5e-4b4e-967c-4a7e9d51f528
-- title:
--   Coprime Basis Existence: is Principal Ideal Ring loc
-- statement:
--   The Coprime Basis Existence construction uses the is Principal Ideal Ring loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsPrincipalIdealRingLoc.lean#L46-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsPrincipalIdealRingLoc.lean#L46-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoprimeBasisExistence
open NumberField nonZeroDivisors

theorem GlobalTheory.CoprimeBasisExistence.isPrincipalIdealRing_loc {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 K) R]
    [IsLocalization (coprimeSet (𝓞 K) m) R] : IsPrincipalIdealRing R := by sorry
