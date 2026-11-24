-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiagDom_perturb_bound
-- name    : GlobalTheory.CompanionTheory.DiagDom.perturb_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:22.599634+00:00
-- url     : https://prove2.me/theorems/774f6ecd-4835-479a-8d06-87e32007c36f
-- title:
--   Diag Dom: perturb bound
-- statement:
--   The Diag Dom construction uses the perturb bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolution.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolution.lean#L5-L18

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiagDom

theorem GlobalTheory.CompanionTheory.DiagDom.perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by sorry
