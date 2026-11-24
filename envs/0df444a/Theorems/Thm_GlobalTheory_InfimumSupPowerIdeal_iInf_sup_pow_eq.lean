-- Prove2me | Theorems.Thm_GlobalTheory_InfimumSupPowerIdeal_iInf_sup_pow_eq
-- name    : GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:07.976904+00:00
-- url     : https://prove2.me/theorems/72559582-4ea4-4555-9a4a-5140fd8121f4
-- title:
--   Infimum Sup Power Ideal: i Inf sup pow eq
-- statement:
--   The Infimum Sup Power Ideal construction uses the i Inf sup pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEq.lean#L5-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEq.lean#L5-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InfimumSupPowerIdeal

theorem GlobalTheory.InfimumSupPowerIdeal.iInf_sup_pow_eq (C : Type) [CommRing C] (J : Ideal C) (hJ : IsAdicComplete J C)
    (u : ℕ → Ideal C) (hu : ∀ e : ℕ, u e = u (e + 1) ⊔ J ^ (e + 1)) (e : ℕ) :
    (⨅ l : ℕ, u l) ⊔ J ^ (e + 1) = u e := by sorry
