-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ZetaPole_not_injective_double_primes
-- name    : GlobalTheory.Mem.ZetaPole.not_injective_double_primes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:34.431912+00:00
-- url     : https://prove2.me/theorems/760465b3-eee5-43c0-b656-d94d0f96c19c
-- title:
--   Zeta Pole: not injective double primes
-- statement:
--   The Zeta Pole construction uses the not injective double primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L91-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean#L91-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ZetaPole

theorem GlobalTheory.Mem.ZetaPole.not_injective_double_primes :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by sorry
