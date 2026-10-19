-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty
-- name    : MIPRE.Introspection.TypeGraph.edges_nonempty
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:33.700035+00:00
-- url     : https://prove2.me/theorems/cf9582b7-4ab9-4165-a073-a961e4b6965b
-- title:
--   Every introspection graph is nonempty, even with no hiding levels
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.TypeGraph` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The introspection type graph. The graph of `introspection.tex`, Figure `fig:type-graph-intro`: the Pauli subgraph, two chains from Pauli-X through hiding levels to Read, two chains from Pauli-Z through Sample and Introspect to Read, the cross-introspection edge, and a loop at every vertex. The construction uses only the Pauli graph and its two distinguished vertices; no rigidity conclusion is assumed.
--
--   Every introspection graph is nonempty, even with no hiding levels.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypeGraph
--   open MIPRE.Introspection.QuestionType Finset
--   variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
--   variable [Fintype PauliType]
--
--   theorem MIPRE.Introspection.TypeGraph.edges_nonempty (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :
--       (edges E X Z ℓ).Nonempty
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypeGraph.edges_nonempty` is declared in `MIPRE/Foundations/Introspection/TypeGraph.lean`, lines 132–136. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/TypeGraph.lean#L132-L136; blueprint lem:intro-type-presentation

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypeGraph
open MIPRE.Introspection.QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
variable [Fintype PauliType]

theorem MIPRE.Introspection.TypeGraph.edges_nonempty (E : PauliType → PauliType → Bool) (X Z : PauliType) (ℓ : ℕ) :
    (edges E X Z ℓ).Nonempty := by sorry
