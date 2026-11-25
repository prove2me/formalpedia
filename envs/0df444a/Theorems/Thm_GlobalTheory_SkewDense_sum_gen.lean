-- Prove2me | Theorems.Thm_GlobalTheory_SkewDense_sum_gen
-- name    : GlobalTheory.SkewDense.sum_gen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:06.206396+00:00
-- url     : https://prove2.me/theorems/dfc03cfb-53a6-4c42-9396-84fd5a15236c
-- title:
--   Skew Dense: sum gen
-- statement:
--   The Skew Dense construction uses the sum gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L57-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L57-L72

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.SkewDense

theorem GlobalTheory.SkewDense.sum_gen {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {κ : Type} [Fintype κ] (b : κ → E)
    (g : E →+* ℂ) (z : Fin n × Fin n × κ → ℂ) (i j : Fin n) :
    ∑ G : Fin n × Fin n × κ, z G * g (gen σ G.1 G.2.1 (b G.2.2) i j) =
      ∑ k, z (i, j, k) * g (b k) - ∑ k, z (j, i, k) * g (σ (b k)) := by sorry
