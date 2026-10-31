-- Prove2me | Theorems.Thm_MCA_summation_theorem
-- name    : MCA.summation_theorem
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T11:35:54.797413+00:00
-- url     : https://prove2.me/theorems/10d2dad6-e860-43dd-b912-a44886f2a565
-- title:
--   Summation theorem for metabolic control
-- statement:
--   This theorem formalizes the summation identities in the finite-dimensional matrix notation of Liu, Theorem 1.
--
--   Let A in R^(m x m) be the state Jacobian, B in R^(m x n) the parameter Jacobian, R in R^(1 x m) and P in R^(1 x n) the output derivatives, and let X in R^(m x n) and T in R^(1 x n) be the corresponding total derivatives. Assume that Ainv is a two-sided inverse of A, that AX+B=0, and that T=RX+P. If every row of B is homogeneous of degree zero with respect to e, and P is homogeneous of degree one with weighted value j, then the four displayed conclusions hold:
--   X=-Ainv B; every row satisfies sum_k e_k X_ik=0; T=-(R Ainv)B+P; and sum_k e_k T_0k=j.
--   The finite sums range over k in Fin n and the matrix identities use the dimensions shown in the formal statement. This is the algebraic summation theorem corresponding to equations (3), (4), (7), and (8) of the source.
--
--   Formalization Note: the theorem uses an explicit matrix Ainv with left- and right-inverse hypotheses; it does not rely on a library inverse operation.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Section 2, Theorem 1, equations (3), (4), (7), and (8). https://arxiv.org/abs/2501.12519

import Mathlib
open scoped BigOperators
open Matrix
namespace MCA

theorem summation_theorem
    {n m : ℕ}
    (e : Fin n → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin m) (Fin n) ℝ)
    (R : Matrix (Fin 1) (Fin m) ℝ)
    (P : Matrix (Fin 1) (Fin n) ℝ)
    (T : Matrix (Fin 1) (Fin n) ℝ)
    (j : ℝ)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hA_left : Ainv * A = 1)
    (hA_right : A * Ainv = 1)
    (hF_chain : A * X + B = 0)
    (hJ_chain : T = R * X + P)
    (hF_hom : ∀ i, ∑ k, e k * B i k = 0)
    (hJ_hom : ∑ k, e k * P 0 k = j) :
    X = -Ainv * B ∧
      (∀ i, ∑ k, e k * X i k = 0) ∧
      T = -(R * Ainv) * B + P ∧
      (∑ k, e k * T 0 k = j) := by sorry

end MCA
