-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_prep_identity
-- name    : GlobalTheory.PMonE.prep_identity
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:58.776163+00:00
-- url     : https://prove2.me/theorems/19853627-994c-4a7c-a560-b560fbaa7255
-- title:
--   PMon E: prep identity
-- statement:
--   The PMon E construction uses the prep identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L155-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L155-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [IsUltrametricDist F]

theorem GlobalTheory.PMonE.prep_identity (p : ℕ) [Fact p.Prime] [CharP F p] (e D : ℕ) (M U : ℕ → Matrix m m F) (A : Matrix m m F)
    (hD : U D = 0) (hU : ∀ n, n < D → U n = M (n + 1) + U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)))
    (h0 : M 0 = -(U 0 * A)) (x : m → F) :
    gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by sorry
