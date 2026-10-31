-- Prove2me | Theorems.Thm_MCA_connectivity_theorem
-- name    : MCA.connectivity_theorem
-- status  : Open
-- author  : @chenyu
-- created : 2026-10-30T11:36:08.216761+00:00
-- url     : https://prove2.me/theorems/9bb9afd4-d7d4-42c0-9eed-abfdead90bea
-- title:
--   General connectivity theorem
-- statement:
--   This is the main connectivity theorem, corresponding to equations (12) and (13) of the source. Let Fv, vS, ve, Se, and W be the finite real matrices shown in the formal statement. Assume Fv vS and ve have explicit two-sided inverses, (Fv vS)Se+Fv ve=0, and W=vS Se+ve. Then (Se veInv)vS=-I_m and (W veInv)vS=0. The second identity is the total-rate/partial-rate connectivity identity.
-- source:
--   Weijiu Liu, Simple Proofs of the Summation and Connectivity Theorems in Metabolic Control Analysis, arXiv:2501.12519v2, Section 3, Theorem 2, equations (12) and (13). https://arxiv.org/abs/2501.12519

import Mathlib
open scoped BigOperators
open Matrix
namespace MCA

theorem connectivity_theorem
    {n m : ℕ}
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
    (h_total : W = vS * Se + ve) :
    (Se * veInv) * vS = -1 ∧
      (W * veInv) * vS = 0 := by sorry

end MCA
