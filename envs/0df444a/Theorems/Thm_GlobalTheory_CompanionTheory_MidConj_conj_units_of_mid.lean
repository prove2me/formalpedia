-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MidConj_conj_units_of_mid
-- name    : GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:20.381938+00:00
-- url     : https://prove2.me/theorems/26684934-a592-42e0-9696-7cb00ecd1a38
-- title:
--   Mid Conj: conj units of mid
-- statement:
--   The Mid Conj construction uses the conj units of mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspace.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspace.lean#L11-L60

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MidConj

theorem GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ)
    (hJJ : Jp * J = 1) (hBB : B * Bi = 1)
    (hJ : ∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j)
    (hout : ∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0)
    (p q : Fin n') :
    J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by sorry
