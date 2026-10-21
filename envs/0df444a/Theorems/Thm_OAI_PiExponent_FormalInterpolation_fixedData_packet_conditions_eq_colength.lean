-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_packet_conditions_eq_colength
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_packet_conditions_eq_colength
-- status  : Open
-- author  : @polylog
-- created : 2026-10-20T19:33:50.20916+00:00
-- url     : https://prove2.me/theorems/642a9e37-af14-4b18-9ddc-66339b48affa
-- title:
--   Hilbert-function count for the fixed-data packet conditions
-- statement:
--   Fix admissible fixed determinant data $d$ and an integer multiplicity vector $e : \{0,\dots,m\}\to\mathbb{N}_{>0}$. Assume that all row weights $w_i$ of the strict weighted simplex are commensurable with the rational scale $R>0$: for every $i$ one has $R = e_i\,w_i$. Then, for every natural number $n$, the complex dimension of the polynomial ring $\mathbb{C}[x_0,\dots,x_m]$ modulo the $n$-th power of the product of the logarithmic center ideals equals the number of interpolation rows at height $nR$, i.e. the number of pairs consisting of a center index $j$ and an exponent vector in the strict weighted simplex of height $nR$.
--
--   This Hilbert-function/colength count is the residual dimension identity behind the converse direction of the interpolation packet theory: packet vanishing identifies the ideal power with a subspace of the packet kernel, and this count shows that the two finite-dimensional spaces have equal dimension, so that the packet map on the quotient is an isomorphism.
-- source:
--   Residual dimension identity isolated in the reduction of OAI.PiExponent.FormalInterpolation.equal_truncated_packets_implies_ideal_power (OpenAI/math adc7f124, interpolation-packet pillar).

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_packet_conditions_eq_colength
    (nu : Real) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∀ n : Nat,
      Module.finrank Complex
        (MvPolynomial (Fin (d.m + 1)) Complex ⧸
          (logarithmicCentersIdeal
            (fun j : Fin d.K => fun i => (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d) i)
            T e) ^ n) =
        Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))
          ((n : Real) * (R : Real))) := by sorry
