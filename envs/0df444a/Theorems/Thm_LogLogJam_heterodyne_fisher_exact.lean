-- Prove2me | Theorems.Thm_LogLogJam_heterodyne_fisher_exact
-- name    : LogLogJam.heterodyne_fisher_exact
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:56:04.645933+00:00
-- url     : https://prove2.me/theorems/1d9a2a38-cafb-5024-b969-0b3826a33cca
-- title:
--   Exact pointwise Fisher information for product heterodyne measurements
-- statement:
--   For squeezing parameter λ>1, measuring k copies independently with the vacuum identity seed gives angular Fisher information k(4E−2) at every angle θ, where E=(λ+λ⁻¹)/4. This includes the empty batch k=0.
-- source:
--   Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983, Section 6.1, Lemma 6.1. This pointwise identity specializes the centered Gaussian covariance formula to the identity seed. https://arxiv.org/abs/2607.12983

import Definitions.Def_LogLogJam_Obs
open Matrix
open scoped ENNReal

namespace LogLogJam
theorem heterodyne_fisher_exact (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (θ : ℝ) :
    measFisher lam k (fun i j => (1 : Matrix (Q k) (Q k) ℝ) i j) θ = ENNReal.ofReal ((k:ℝ)*(4*energy lam-2)) := by sorry
end LogLogJam
