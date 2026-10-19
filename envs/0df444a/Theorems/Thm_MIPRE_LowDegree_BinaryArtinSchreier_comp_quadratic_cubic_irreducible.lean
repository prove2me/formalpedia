-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_comp_quadratic_cubic_irreducible
-- name    : MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:19.238103+00:00
-- url     : https://prove2.me/theorems/1e7c326f-0588-4a4f-9f12-6dff34ef6cbe
-- title:
--   Flattening the quadratic extension preserves the cubic no-root invariant
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryArtinSchreier` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The characteristic-two Artin–Schreier tower step. The polynomial `X² + X + a` has no root exactly when its quadratic quotient is an extension field. In that extension, multiplication of `a` by the canonical root supplies the next no-root parameter. These are algebraic correctness lemmas for the explicit binary tower constructor; they do not choose a root by searching through the field.
--
--   Flattening the quadratic extension preserves the cubic no-root invariant.
--   Only the canonical embedding of the flat quotient is required; no search for
--   an isomorphism or a field element is part of this argument.
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
--   theorem MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible [Finite K] [Algebra (ZMod 2) K]
--       [FiniteDimensional (ZMod 2) K] (t : ℕ)
--       (hK : Module.finrank (ZMod 2) K = 2 ^ t)
--       (a : K) (ha : Irreducible (quadratic a))
--       (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
--       (hz : aeval a g = 0) :
--       let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
--         ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
--       Irreducible (quadratic
--         (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 3 +
--           AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 2))
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible` is declared in `MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean`, lines 200–237. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryArtinSchreier.lean#L200-L237

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

theorem MIPRE.LowDegree.BinaryArtinSchreier.comp_quadratic_cubic_irreducible [Finite K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (t : ℕ)
    (hK : Module.finrank (ZMod 2) K = 2 ^ t)
    (a : K) (ha : Irreducible (quadratic a))
    (g : (ZMod 2)[X]) (hg : g.Monic) (hd : g.natDegree = 2 ^ t)
    (hz : aeval a g = 0) :
    let : Fact (Irreducible (g.comp (quadratic (0 : ZMod 2)))) :=
      ⟨comp_quadratic_irreducible t hK a ha g hg hd hz⟩
    Irreducible (quadratic
      (AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 3 +
        AdjoinRoot.root (g.comp (quadratic (0 : ZMod 2))) ^ 2)) := by sorry
