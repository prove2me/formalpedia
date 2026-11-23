-- Prove2me | Theorems.Thm_IActThereforeIAm_gaussian_score
-- name    : IActThereforeIAm.gaussian_score
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:08:05.824946+00:00
-- url     : https://prove2.me/theorems/5197dd0b-c72c-415f-9461-8f6608a64ad4
-- title:
--   Eq. (10): first and second derivatives of the Gaussian log-density
-- statement:
--   Let $q(u)=\log\mathcal N(u;m,v)$ be the log-density of a Gaussian with mean $m$ and variance $v>0$. Then for every $u\in\mathbb R$,
--
--   $$q'(u)=-\frac{u-m}{v},\qquad q''(u)=-\frac1v.$$
--
--   Applied to the action-modulated Gaussian additive-noise model, with $m=f_i(\mathbf s_{t-1,\mathrm{pa}_i},\mathbf a_{t-1})$ and $v=\sigma_i^2(\mathbf a_{t-1})$, this gives the entries of the vector $\mathbf w$ in Assumption 3.2.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Section 4, Eq. (10), p. 5

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem gaussian_score (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (u : ℝ) :
    deriv (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -(u - m) / v ∧
    deriv (deriv fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -1 / v := by sorry

end IActThereforeIAm
