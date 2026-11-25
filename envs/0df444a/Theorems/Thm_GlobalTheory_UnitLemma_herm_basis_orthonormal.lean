-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_herm_basis_orthonormal
-- name    : GlobalTheory.UnitLemma.herm_basis_orthonormal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:24.471738+00:00
-- url     : https://prove2.me/theorems/ce1007ac-33a8-46ea-bd74-65875fb7d94d
-- title:
--   Unit Lemma: herm basis orthonormal
-- statement:
--   The Unit Lemma construction uses the herm basis orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L51-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L51-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
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
open GlobalTheory.UnitLemma.OrthBasis

theorem GlobalTheory.UnitLemma.herm_basis_orthonormal : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by sorry
