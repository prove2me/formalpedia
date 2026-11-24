-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_torusOrb_UU_eq_finsum
-- name    : GlobalTheory.UnitLemma.InvAlg.torusOrb_UU_eq_finsum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:30.225206+00:00
-- url     : https://prove2.me/theorems/d43ca77d-5e3f-4fb7-af7e-5fdf499c5871
-- title:
--   Inv Alg: torus Orb UU eq finsum
-- statement:
--   The Inv Alg construction uses the torus Orb UU eq finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UUEqSumOverTorusOrbits.lean#L119-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UUEqSumOverTorusOrbits.lean#L119-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UUEqSumOverTorusOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
open GlobalTheory.UnitLemma.InvAlg
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.UnitLemma.InvAlg.torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by sorry
