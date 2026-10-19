-- Prove2me | Theorems.Thm_MIPRE_LCS_Pauli_X_anticomm_Z
-- name    : MIPRE.LCS.Pauli.X_anticomm_Z
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:54.669857+00:00
-- url     : https://prove2.me/theorems/6fd56013-6631-478e-acd3-764206a9bf30
-- title:
--   Lemma X_anticomm_Z of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.LCS.Pauli` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli Matrices. This module defines the single-qubit Pauli matrices `Pauli.I`, `Pauli.X`, `Pauli.Y`, `Pauli.Z`, together with their multiplication table, anticommutation relations, and observable structure. It also records the Kronecker-product lemmas used to combine commuting or anticommuting pairs into commuting two-qubit observables.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LCS
--   open MIPRE.LCS.Pauli
--   open Matrix
--   open scoped Kronecker
--
--   theorem MIPRE.LCS.Pauli.X_anticomm_Z : X * Z = -(Z * X)
--   ```
--
--   **Formalization Note** `MIPRE.LCS.Pauli.X_anticomm_Z` is declared in `MIPRE/LCS/Pauli.lean`, lines 137–139. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Pauli.lean#L137-L139

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Pauli

open MIPRE
open MIPRE.LCS
open MIPRE.LCS.Pauli
open Matrix
open scoped Kronecker

theorem MIPRE.LCS.Pauli.X_anticomm_Z : X * Z = -(Z * X) := by sorry
