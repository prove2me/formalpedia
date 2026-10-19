-- Prove2me | Theorems.Thm_MIPRE_Introspection_QuestionType_card
-- name    : MIPRE.Introspection.QuestionType.card
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:55.756759+00:00
-- url     : https://prove2.me/theorems/d1b56933-190e-4b03-a45d-c903e1f35fb8
-- title:
--   Introspection contributes exactly 2ℓ + 6 vertices
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.Types` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The introspection question types. The source's type set consists of the Pauli types and two copies of `Introspect`, `Sample`, `Read`, and `Hide₁, ..., Hideℓ`. The Pauli type is a parameter so the foundational construction can be instantiated with the concrete Pauli test without importing a Background module.
--
--   Introspection contributes exactly `2ℓ + 6` vertices.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.QuestionType
--   variable {PauliType : Type*} {ℓ : ℕ}
--
--   theorem MIPRE.Introspection.QuestionType.card [Fintype PauliType] (ℓ : ℕ) :
--       Fintype.card (QuestionType PauliType ℓ) = Fintype.card PauliType + 2 * ℓ + 6
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.QuestionType.card` is declared in `MIPRE/Foundations/Introspection/Types.lean`, lines 100–104. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Types.lean#L100-L104; blueprint lem:intro-type-presentation

import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Introspection_Types

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.QuestionType
variable {PauliType : Type*} {ℓ : ℕ}

theorem MIPRE.Introspection.QuestionType.card [Fintype PauliType] (ℓ : ℕ) :
    Fintype.card (QuestionType PauliType ℓ) = Fintype.card PauliType + 2 * ℓ + 6 := by sorry
