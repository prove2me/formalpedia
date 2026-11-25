-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SmallBlockEigenvalues_rowEigSmall_of_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:18.014837+00:00
-- url     : https://prove2.me/theorems/667df8af-aeb5-41a6-a7f1-3a47c49a3783
-- title:
--   Small Block Eigenvalues: row Eig Small of le
-- statement:
--   The Small Block Eigenvalues construction uses the row Eig Small of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/SmallRowEigenvalues.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/SmallRowEigenvalues.lean#L23-L34

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

theorem GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues.rowEigSmall_of_le {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N)
    (h : ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
      ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
        ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((R.r : ℝ) - 1) / 2)) :
    RowEigSmall N A := by sorry
