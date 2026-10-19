-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryDegreeFactors_degreeFactors_prod
-- name    : MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:20.447878+00:00
-- url     : https://prove2.me/theorems/b072451e-6036-493c-9e4d-28f680b6797c
-- title:
--   The complete bounded list reconstructs every positive input degree
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryDegreeFactors` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Prime-power degree decomposition. This list is used only in the proof of the all-degrees constructor. The executable constructor computes the same prime-power factors by bounded unary arithmetic. Indices outside the prime support contribute the neutral factor one.
--
--   The complete bounded list reconstructs every positive input degree.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryDegreeFactors
--
--   theorem MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod (n : ℕ) (hn : 0 < n) : (degreeFactors n).prod = n
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod` is declared in `MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean`, lines 23–36. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryDegreeFactors.lean#L23-L36; blueprint lem:binary-degree-decomposition

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryDegreeFactors

theorem MIPRE.LowDegree.BinaryDegreeFactors.degreeFactors_prod (n : ℕ) (hn : 0 < n) : (degreeFactors n).prod = n := by sorry
