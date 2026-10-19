-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_next_quadratic_irreducible
-- name    : MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:16.208642+00:00
-- url     : https://prove2.me/theorems/8f1c9e69-212a-495e-bc19-b9089b41163f
-- title:
--   One no-root quadratic gives the next one over its explicitly presented extension
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreier` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The characteristic-two Artin–Schreier tower step. The polynomial `X² + X + a` has no root exactly when its quadratic quotient is an extension field. In that extension, multiplication of `a` by the canonical root supplies the next no-root parameter. These are algebraic correctness lemmas for the explicit binary tower constructor; they do not choose a root by searching through the field.
--
--   One no-root quadratic gives the next one over its explicitly presented extension.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryArtinSchreier
--   open Polynomial Module
--   variable {K : Type*} [Field K]
--   variable [CharP K 2]
--
--   theorem MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
--       let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
--       Irreducible (quadratic
--         (algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a)))
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible` is declared in `MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean`, lines 96–115. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean#L96-L115

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryArtinSchreier
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]

theorem MIPRE.LowDegree.BinaryArtinSchreier.next_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a))) := by sorry
