-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_totalDegree_substF_le
-- name    : GlobalTheory.CompactHowe.totalDegree_substF_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:41.706502+00:00
-- url     : https://prove2.me/theorems/f0de7076-8952-4e79-89fc-070ca9199a45
-- title:
--   Compact Howe: total Degree subst F le
-- statement:
--   The Compact Howe construction uses the total Degree subst F le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TotalDegreeSubstFLe.lean#L36-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
variable {ι : Type} {N n : ℕ}

theorem GlobalTheory.CompactHowe.totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree := by sorry
