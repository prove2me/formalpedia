-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_padicInt_domain_embedding
-- name    : GlobalTheory.T.exists_finite_padicInt_domain_embedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:57.034774+00:00
-- url     : https://prove2.me/theorems/6192be64-1234-45bd-97dc-cdc20912f7ab
-- title:
--   T: exists finite padic Int domain embedding
-- statement:
--   The T construction uses the exists finite padic Int domain embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbeddingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbeddingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbeddingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by sorry
