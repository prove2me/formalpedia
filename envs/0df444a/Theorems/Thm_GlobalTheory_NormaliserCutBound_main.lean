-- Prove2me | Theorems.Thm_GlobalTheory_NormaliserCutBound_main
-- name    : GlobalTheory.NormaliserCutBound.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:39.892205+00:00
-- url     : https://prove2.me/theorems/9c5a9fdb-3ad8-47fe-bf31-788319f65c67
-- title:
--   Normaliser Cut Bound: main
-- statement:
--   The Normaliser Cut Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdFinEqProdIcc.lean#L26-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdFinEqProdIcc.lean#L26-L105

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdFinEqProdIcc
import Theorems.Thm_GlobalTheory_BracketBound_main
import Theorems.Thm_GlobalTheory_CloudProd_main
import Theorems.Thm_GlobalTheory_LamSize_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory GlobalTheory.NormaliserCutBound

theorem GlobalTheory.NormaliserCutBound.main : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by sorry
