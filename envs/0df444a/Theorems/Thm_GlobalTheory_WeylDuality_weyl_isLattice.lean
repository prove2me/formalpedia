-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_weyl_isLattice
-- name    : GlobalTheory.WeylDuality.weyl_isLattice
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:56:11.495031+00:00
-- url     : https://prove2.me/theorems/6e2109a9-05fd-471d-bf94-3c4637abbdf6
-- title:
--   Weyl Duality: weyl is Lattice
-- statement:
--   The Weyl Duality construction uses the weyl is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L261-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L261-L293

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.weyl_isLattice {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    (inV ν ((weyl ℤ r n hn ν).map (intQ r n))).IsLattice ℚ := by sorry
