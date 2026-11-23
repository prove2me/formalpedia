-- Prove2me | Theorems.Thm_IActThereforeIAm_data_processing_representation
-- name    : IActThereforeIAm.data_processing_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:04:26.330801+00:00
-- url     : https://prove2.me/theorems/2ad90e45-0e25-497e-8010-119c53bc79d4
-- title:
--   Eq. (18): data processing for the representation
-- statement:
--   Let the latent model be valid, and let $\mathbf g$ and $\mathbf h$ be measurable. Set $\mathbf z_t=\mathbf h(\mathbf g(\mathbf s_t))$ and $\mathbf z_{t-1}=\mathbf h(\mathbf g(\mathbf s_{t-1}))$. Then
--
--   $$I(\mathbf z_t;\mathbf z_{t-1},\mathbf a_{t-1})\le I(\mathbf s_t;\mathbf z_{t-1},\mathbf a_{t-1})\le I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1}).$$
--
--   This is the data-processing inequality applied to each argument of the mutual information. It shows that the representation never carries more transition information than the latent state.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix C (proof of Theorem 2.1), Eq. (18), p. 18

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem data_processing_representation {d : ℕ} {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (M : LatentSCM d A) (hM : M.IsValid) (g : (Fin d → ℝ) → X)
    (hg : Measurable g) (h : X → Fin d → ℝ) (hh : Measurable h) :
    reprInfo M g h ≤ mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ∧
    mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ≤ latentInfo M := by sorry

end IActThereforeIAm
