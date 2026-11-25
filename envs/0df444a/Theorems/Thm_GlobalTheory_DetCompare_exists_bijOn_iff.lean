-- Prove2me | Theorems.Thm_GlobalTheory_DetCompare_exists_bijOn_iff
-- name    : GlobalTheory.DetCompare.exists_bijOn_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:52.305807+00:00
-- url     : https://prove2.me/theorems/dfa121c3-38f0-4e91-aa98-b5769e322acb
-- title:
--   Det Compare: exists bij On iff
-- statement:
--   The Det Compare construction uses the exists bij On iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L18-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]

theorem GlobalTheory.DetCompare.exists_bijOn_iff (W : Submodule k N) (n : ℕ) :
    (∃ v : Fin n → N, (∀ i, v i ∈ W) ∧ Set.BijOn (fun c : Fin n → k => ∑ i, c i • v i) Set.univ W) ↔
      Module.Finite k W ∧ Module.finrank k W = n := by sorry
