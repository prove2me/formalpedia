-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_ideal_map_comap_of_stable
-- name    : GlobalTheory.GaloisDescent.ideal_map_comap_of_stable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:47:40.493774+00:00
-- url     : https://prove2.me/theorems/cac94c4e-a3dd-43f4-9e4b-4803bf180bee
-- title:
--   Galois Descent: ideal map comap of stable
-- statement:
--   The Galois Descent construction uses the ideal map comap of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/MvPolynomialIsHomogeneousComapWeighted.lean#L63-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem GlobalTheory.GaloisDescent.ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I := by sorry
