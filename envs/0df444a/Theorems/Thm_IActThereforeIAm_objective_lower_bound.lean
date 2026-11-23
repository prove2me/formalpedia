-- Prove2me | Theorems.Thm_IActThereforeIAm_objective_lower_bound
-- name    : IActThereforeIAm.objective_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:05:05.454813+00:00
-- url     : https://prove2.me/theorems/28335edc-4333-426a-92b1-bb8955bd7387
-- title:
--   Eq. (21): the JEPA objective is bounded below by $-I(s_t;s_{t-1},a_{t-1})$
-- statement:
--   Let the latent model be valid, let $\mathbf g$ be measurable, let $\lambda\ge1$, and let $(\mathbf h,p)$ be an admissible pair: an encoder $\mathbf h:\mathcal X\to(0,1)^d$ and a transition model $p$ for which both terms of Eq. (4) are finite. Then
--
--   $$\mathcal L_\lambda(\mathbf h,p)\ge-I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1}).$$
--
--   The bound combines the decomposition of the objective into a mutual-information term, an expected KL divergence and an entropy term (Eq. 17) with data processing (Eq. 18) and the entropy bound (Eq. 19).
--
--   **Formalization Note** Admissibility encodes the paper's implicit requirement that the objective be finite. If $I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1})=\infty$ the bound is trivial.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix C (proof of Theorem 2.1), Eqs. (17)-(21), p. 18

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem objective_lower_bound {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (M : LatentSCM d A) (hM : M.IsValid) (g : (Fin d → ℝ) → X) (hg : Measurable g)
    (lam : ℝ) (hlam : 1 ≤ lam) (h : X → Fin d → ℝ) (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ)
    (hadm : IsAdmissible M g h p) :
    -((latentInfo M : ℝ≥0∞) : EReal) ≤ ((objective M g lam h p : ℝ) : EReal) := by sorry

end IActThereforeIAm
