-- Prove2me | Theorems.Thm_InverseGalois_exists_regularFractionField_embedding_complex
-- name    : InverseGalois.exists_regularFractionField_embedding_complex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:39:48.958735+00:00
-- url     : https://prove2.me/theorems/f55d2a39-5122-43b1-9d62-d6acfda4d32a
-- title:
--   The regular rational-function field embeds into the complex numbers
-- statement:
--   For every finite group $G$, the rational-function field over $ℚ$ whose variables are indexed by the regular $G$-set admits a rational field embedding into the complex numbers:
--
--   $$
--   ℚ(X_g : g∈G) ↪ ℂ.
--   $$
--
--   This supplies a concrete complex copy of the ambient field used in the regular inverse-Galois construction.
-- source:
--   Mathlib, evaluation at an algebraically independent family, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AlgebraicIndependent/Defs.lean#L136-L145; extension to a fraction field, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/FractionRing.lean#L365-L378

import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_exists_algebraicallyIndependent_complex_family

namespace InverseGalois

universe u

theorem exists_regularFractionField_embedding_complex
    (G : Type u) [Fintype G] [Group G] :
    Nonempty (RegularFractionField G →ₐ[ℚ] ℂ) := by sorry
