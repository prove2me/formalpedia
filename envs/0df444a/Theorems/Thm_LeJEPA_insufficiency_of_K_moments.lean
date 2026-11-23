-- Prove2me | Theorems.Thm_LeJEPA_insufficiency_of_K_moments
-- name    : LeJEPA.insufficiency_of_K_moments
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:11:15.21016+00:00
-- url     : https://prove2.me/theorems/7a66d87b-719e-45aa-947d-3a28dbb70f00
-- title:
--   Theorem 3: matching finitely many moments does not identify the distribution
-- statement:
--   For every $K\in\mathbb{N}$ and all weights $c_k>0$ there is a probability measure $P$ on $\mathbb{R}$, with finite moments up to order $K$ and $P\neq\mathcal N(0,1)$, at which the moment-matching objective vanishes:
--
--   $$\sum_{k=1}^{K}c_k\big(m_k(P)-m_k(\mathcal N(0,1))\big)^2=0 .$$
--
--   Driving a finite moment-matching loss to its minimum therefore does not force the projected embedding distribution to be the Gaussian target.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Section 4.2.1, Theorem 3, proof in Appendix B.11; $Q^{(a)}$ is the standard Gaussian target

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem insufficiency_of_K_moments (K : ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) :
    ∃ P : Measure ℝ, IsProbabilityMeasure P ∧ (∀ k ≤ K, Integrable (fun x => x ^ k) P) ∧
      ∑ k ∈ Finset.Icc 1 K, c k * (rawMoment k P - rawMoment k (ProbabilityTheory.gaussianReal 0 1)) ^ 2 = 0 ∧
      P ≠ ProbabilityTheory.gaussianReal 0 1 := by sorry

end LeJEPA
