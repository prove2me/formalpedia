-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plainJet_shifted_product_eq_Xprod
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_product_eq_Xprod
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T21:59:25.986979+00:00
-- url     : https://prove2.me/theorems/dfbbb46e-8545-4ad7-9099-df7088464bb7
-- title:
--   Plain jet evaluates shifted coordinate products
-- statement:
--   Applying `plainJet` to a scalar times a product of powers of coordinates shifted by the jet center gives the same scalar times the product of the corresponding formal variables to those powers. The statement includes zero exponents and the empty product.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plainJet_shifted_product_eq_Xprod
    {m : Nat} (c : Fin m -> Complex) (a : Complex)
    (d : Fin (m + 1) -> Nat) :
    OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.C a *
          Finset.prod Finset.univ (fun k : Fin (m + 1) =>
            (MvPolynomial.X k -
              MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ d k)) =
      MvPowerSeries.C a *
        Finset.prod Finset.univ (fun k : Fin (m + 1) =>
          (MvPowerSeries.X k) ^ d k) := by sorry
