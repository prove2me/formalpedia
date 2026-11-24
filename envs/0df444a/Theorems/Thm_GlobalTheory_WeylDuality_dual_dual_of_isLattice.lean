-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_dual_dual_of_isLattice
-- name    : GlobalTheory.WeylDuality.dual_dual_of_isLattice
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:32.114254+00:00
-- url     : https://prove2.me/theorems/cfe78513-ca65-40fc-9c87-5fc611ad62f4
-- title:
--   Weyl Duality: dual dual of is Lattice
-- statement:
--   The Weyl Duality construction uses the dual dual of is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L182-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L182-L196

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

theorem GlobalTheory.WeylDuality.dual_dual_of_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (hB : B.Nondegenerate) (hB' : B.IsSymm) (M : Submodule ℤ V) [M.IsLattice ℚ] :
    B.dualSubmodule (B.dualSubmodule M) = M := by sorry
