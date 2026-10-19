-- Prove2me | Theorems.Thm_MIPRE_SAT_PcpAlgebra_degreeOf_constraint_le
-- name    : MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:04.577865+00:00
-- url     : https://prove2.me/theorems/2c396103-aa5f-4b2a-a6cb-ecedef717a28
-- title:
--   The conservative individual-degree bound used in the source's soundness proof
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.PcpAlgebra` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The algebraic tests of the classical PCP. The formula test and Boolean-cube zero test from `thm:pcp-decider`. These lemmas concern polynomials and their evaluations. Circuit padding, the embedding of the five answer blocks, and the verifier's ambient program are separate obligations.
--
--   The conservative individual-degree bound used in the source's soundness proof.
--   It does not rely on disjointness of the five blocks.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.PcpAlgebra
--   open Finset MvPolynomial MIPRE.LowDegree
--   variable {F : Type*} [Field F] {m : ℕ}
--
--   theorem MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le (φ : MvPolynomial (Fin m) F)
--       (g : Fin 5 → MvPolynomial (Fin m) F) (sign : Fin 5 → Fin m) {d : ℕ}
--       (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d) (j : Fin m) :
--       (constraint φ g sign).degreeOf j ≤ 6 + 5 * max d 1
--   ```
--
--   **Formalization Note** `MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le` is declared in `MIPRE/Foundations/SAT/PcpAlgebra.lean`, lines 56–74. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/PcpAlgebra.lean#L56-L74; blueprint lem:pcp-algebra-tests

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.SAT.PcpAlgebra.degreeOf_constraint_le (φ : MvPolynomial (Fin m) F)
    (g : Fin 5 → MvPolynomial (Fin m) F) (sign : Fin 5 → Fin m) {d : ℕ}
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d) (j : Fin m) :
    (constraint φ g sign).degreeOf j ≤ 6 + 5 * max d 1 := by sorry
