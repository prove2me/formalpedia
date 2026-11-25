-- Prove2me | Theorems.Thm_GlobalTheory_GenEigen_eigen_of_gen_eigen
-- name    : GlobalTheory.GenEigen.eigen_of_gen_eigen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:21.539205+00:00
-- url     : https://prove2.me/theorems/fd4f0693-85c2-4f80-9b1e-f6776e4594cf
-- title:
--   Gen Eigen: eigen of gen eigen
-- statement:
--   The Gen Eigen construction uses the eigen of gen eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EigenvectorOfGeneralizedEigenUnramified.lean#L145-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EigenvectorOfGeneralizedEigenUnramified.lean#L145-L220

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GenEigen
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.GenEigen.eigen_of_gen_eigen (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type)
    [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C) (hL : ∀ x i j, V.Ge 0 (L x i j))
    (d : ℕ) (hd : 0 < d) (ε : O) (h1 : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) (ψ : O →+* C) (w : κ → C)
    (hψ : ∀ x, V.Ge 0 (ψ x))
    (hnil : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0)
    (hlim : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i))
    (x : O) : (L x).mulVec w = ψ x • w := by sorry
