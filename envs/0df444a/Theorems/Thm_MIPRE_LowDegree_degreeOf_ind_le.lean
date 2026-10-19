-- Prove2me | Theorems.Thm_MIPRE_LowDegree_degreeOf_ind_le
-- name    : MIPRE.LowDegree.degreeOf_ind_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:34.19163+00:00
-- url     : https://prove2.me/theorems/d142445f-ca72-4a1d-bbb5-bf1a7f02cf51
-- title:
--   Lemma degreeOf_ind_le of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.Encoding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The low-degree code. The paper's `sec:ld-encoding`: the multilinear indicator polynomials of the Boolean subcube, the *low-degree encoding* `g_a` of a vector indexed by the subcube, and the decoding map `Coded_H`. This is the code the PCP of `thm:pcp-decider` commits to, and the `a = Coded(g₁)` of its soundness conclusion. * `ind y = ∏_{i : yᵢ = 1} Xᵢ · ∏_{i : yᵢ = 0} (1 - Xᵢ)` — on the subcube, `1` at `y` and `0` elsewhere (`eval_ind`); * `pt y` is the subcube point of `y : Fin m → Bool`, identifying `{0,1}` with `{0, 1} ⊆ F`; * `ldEnc a = ∑_y a y · ind y` — the multilinear polynomial with…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F : Type*} [CommRing F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.degreeOf_ind_le [Nontrivial F] (y : Fin m → Bool) (i : Fin m) :
--       (ind y : MvPolynomial (Fin m) F).degreeOf i ≤ 1
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.degreeOf_ind_le` is declared in `MIPRE/Foundations/LowDegree/Encoding.lean`, lines 67–84. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/Encoding.lean#L67-L84; blueprint def:ld-encoding

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

open MIPRE
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}

theorem MIPRE.LowDegree.degreeOf_ind_le [Nontrivial F] (y : Fin m → Bool) (i : Fin m) :
    (ind y : MvPolynomial (Fin m) F).degreeOf i ≤ 1 := by sorry
