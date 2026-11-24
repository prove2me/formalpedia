-- Prove2me | Theorems.Thm_GlobalTheory_LinearIndependentFixed_linearIndepOn_of_fixed
-- name    : GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:00.594248+00:00
-- url     : https://prove2.me/theorems/3ddac2cd-81f7-416a-ba44-5d4498e050e0
-- title:
--   Linear Independent Fixed: linear Indep On of fixed
-- statement:
--   The Linear Independent Fixed construction uses the linear Indep On of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndepOnOfFixed.lean#L5-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndepOnOfFixed.lean#L5-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndepOnOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LinearIndependentFixed

theorem GlobalTheory.LinearIndependentFixed.linearIndepOn_of_fixed {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W]
    [Module.IsTorsionFree B W] (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), σ g (b • w) = a g b • σ g w)
    (hK : ∀ (b b' : B), b ≠ 0 → (∀ g : G, b * a g b' = a g b * b') →
      ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), σ g (v i) = v i)
    (s : Finset ι) (hs : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by sorry
