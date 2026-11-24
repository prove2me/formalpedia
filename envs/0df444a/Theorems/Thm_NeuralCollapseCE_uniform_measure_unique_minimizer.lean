-- Prove2me | Theorems.Thm_NeuralCollapseCE_uniform_measure_unique_minimizer
-- name    : NeuralCollapseCE.uniform_measure_unique_minimizer
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:12:08.919012+00:00
-- url     : https://prove2.me/theorems/66197562-c40a-420c-b12b-91eb8d84caee
-- title:
--   Proposition 4: the uniform measure is the unique minimiser of the relaxed energy
-- statement:
--   Let $d\ge1$, $\alpha>0$, and let $\sigma_d$ be the uniform probability measure on the unit sphere $\mathbb{S}^d\subset\mathbb{R}^d$. For a probability measure $\mu$ on $\mathbb{S}^d$ set
--
--   $$\mathcal{L}_\alpha(\mu)=\int_{\mathbb{S}^d}\log\Big(\int_{\mathbb{S}^d}e^{\alpha(\langle x,y\rangle-1)}\,\mu(dy)\Big)\,\mu(dx).$$
--
--   Then $\sigma_d$ is the unique minimiser of $\mathcal{L}_\alpha$ over $\mathcal P(\mathbb{S}^d)$: $\mathcal{L}_\alpha(\sigma_d)\le\mathcal{L}_\alpha(\mu)$ for every $\mu\in\mathcal P(\mathbb{S}^d)$, and every minimiser equals $\sigma_d$.
--
--   This is the continuum version of the symmetric problem and is the key input of Theorem 3.
--
--   **Formalization Note** The statement also records that $\sigma_d$ is a probability measure, which the paper takes for granted. The hypothesis $d\ge1$ excludes the empty sphere of $\mathbb{R}^0$.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.3, Proposition 4, eq. (3), p. 3; proof in Section 4, p. 9

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem uniform_measure_unique_minimizer {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure (uniformSphere d) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      measureEnergy α (uniformSphere d) ≤ measureEnergy α μ) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      (∀ ν : Measure (Sph d), IsProbabilityMeasure ν → measureEnergy α μ ≤ measureEnergy α ν) →
      μ = uniformSphere d) := by sorry

end NeuralCollapseCE
