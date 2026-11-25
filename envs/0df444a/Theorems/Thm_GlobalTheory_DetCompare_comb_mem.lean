-- Prove2me | Theorems.Thm_GlobalTheory_DetCompare_comb_mem
-- name    : GlobalTheory.DetCompare.comb_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:49.951197+00:00
-- url     : https://prove2.me/theorems/9175503d-70e1-4c9f-a422-bc983ca659fc
-- title:
--   Det Compare: comb mem
-- statement:
--   The Det Compare construction uses the comb mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L93-L96

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
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
variable [IsCommMonObj G]

theorem GlobalTheory.DetCompare.comb_mem {act : OAct O G} {t : Sp k ⟶ S} {τ : O →+* k} {n : ℕ} {v : Fin n → Lie G t}
    (hv : ∀ i, v i ∈ eigenspace act t τ) (c : Fin n → k) : comb v c ∈ eigenspace act t τ := by sorry
