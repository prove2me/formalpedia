-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_irreducible_cyclotomic_prime_pow
-- name    : GroundTheory.PAdicHodge.irreducible_cyclotomic_prime_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:42.583971+00:00
-- url     : https://prove2.me/theorems/f084d42e-49e6-4217-8c8c-8b450cbf1bcc
-- title:
--   PAdic Hodge: irreducible cyclotomic prime pow
-- statement:
--   The PAdic Hodge construction uses the irreducible cyclotomic prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L129-L135

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.irreducible_cyclotomic_prime_pow (n : ℕ) : Irreducible (cyclotomic (p ^ n) ℚ_[p]) := by sorry
