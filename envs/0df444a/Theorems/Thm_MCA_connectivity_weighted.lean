-- Prove2me | Theorems.Thm_MCA_connectivity_weighted
-- name    : MCA.connectivity_weighted
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T11:36:24.98411+00:00
-- url     : https://prove2.me/theorems/e028f7f9-cf97-4fac-a8a9-428672e806c4
-- title:
--   Weighted connectivity identities
-- statement:
--   This theorem is the diagonal-elasticity specialization of the connectivity theorem, corresponding to equations (18) and (19) of the source. Let e,v be parameter and rate coordinates. Assume ve is diagonal, e_i ve(i,i)=v_i, and veInv(i,i)=e_i/v_i, together with the same chain-rule and inverse hypotheses as the general theorem. Then the component sums are -1 on the diagonal and 0 off the diagonal, and the total-rate weighted connectivity sum is zero. Real division is total.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Section 3, Theorem 2, equations (14), (15), (18), and (19). https://arxiv.org/abs/2501.12519

import Mathlib
open scoped BigOperators
open Matrix
namespace MCA

theorem connectivity_weighted
    {n m : ℕ}
    (e v : Fin n → ℝ)
    (Fv : Matrix (Fin m) (Fin n) ℝ)
    (vS : Matrix (Fin n) (Fin m) ℝ)
    (ve : Matrix (Fin n) (Fin n) ℝ)
    (Se : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (veInv : Matrix (Fin n) (Fin n) ℝ)
    (fsInv : Matrix (Fin m) (Fin m) ℝ)
    (hfs_left : fsInv * (Fv * vS) = 1)
    (hfs_right : (Fv * vS) * fsInv = 1)
    (hve_left : veInv * ve = 1)
    (hve_right : ve * veInv = 1)
    (h_chain : (Fv * vS) * Se + Fv * ve = 0)
    (h_total : W = vS * Se + ve)
    (h_offdiag : ∀ i j, i ≠ j → ve i j = 0)
    (h_diag_scale : ∀ i, e i * ve i i = v i)
    (h_inv_entries : ∀ i, veInv i i = e i / v i) :
    (∀ i j, ∑ k, (e k / v k) * Se i k * vS k j = if i = j then -1 else 0) ∧
      (∀ i j, ∑ k, (e k / v k) * W i k * vS k j = 0) := by sorry

end MCA
