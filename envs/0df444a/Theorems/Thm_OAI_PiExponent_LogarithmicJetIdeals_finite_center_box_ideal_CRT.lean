-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_ideal_CRT
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_ideal_CRT
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:59:09.30851+00:00
-- url     : https://prove2.me/theorems/d625d7b3-359e-486a-8b93-6c92b203da0d
-- title:
--   Finite-center interpolation modulo rectangular jet ideals
-- statement:
--   For a finite active family of pairwise distinct centers, one polynomial matches arbitrary local polynomials modulo the respective rectangular jet ideals.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_ideal_CRT
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) ->
      Exists fun k => Not (center i k = center j k))
    (localPoly : iota -> MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        P - localPoly i ∈
          OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal (center i) degree := by sorry
