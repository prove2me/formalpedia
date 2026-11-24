-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_conj_entry
-- name    : GlobalTheory.CompanionTheory.CongIndex.conj_entry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:51.59442+00:00
-- url     : https://prove2.me/theorems/00b3938d-89b1-4dc3-9845-f3c961d05fbc
-- title:
--   Cong Index: conj entry
-- statement:
--   The Cong Index construction uses the conj entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L305-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L305-L333

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}

theorem GlobalTheory.CompanionTheory.CongIndex.conj_entry {ϖ : k} (h0 : ϖ ≠ 0) {a : Fin N → ℤ} {D : GL (Fin N) k}
    (hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)))
    (g : GL (Fin N) k) (i j : Fin N) :
    ((D⁻¹ * g * D : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
        - (1 : Matrix (Fin N) (Fin N) k) i j =
      ϖ ^ (a j - a i) * ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by sorry
