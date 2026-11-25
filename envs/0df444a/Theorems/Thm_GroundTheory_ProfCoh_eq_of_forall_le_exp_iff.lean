-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_eq_of_forall_le_exp_iff
-- name    : GroundTheory.ProfCoh.eq_of_forall_le_exp_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:52.508862+00:00
-- url     : https://prove2.me/theorems/898c94d1-5424-44e6-b7db-f68153ac3fc5
-- title:
--   Prof Coh: eq of forall le exp iff
-- statement:
--   The Prof Coh construction uses the eq of forall le exp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean#L10-L22

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

theorem GroundTheory.ProfCoh.eq_of_forall_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by sorry
