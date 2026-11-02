-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_continuous_lift_of_continuous_mod_one
-- name    : HryniewiczCriterion.exists_continuous_lift_of_continuous_mod_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T16:03:30.269204+00:00
-- url     : https://prove2.me/theorems/7531400b-656f-4a20-890c-59a6df070b6a
-- title:
--   A real function that is continuous modulo 1 differs from a continuous function by integers
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be any function such that $t\mapsto f(t)\bmod 1\in\mathbb{R}/\mathbb{Z}$ is continuous. Then there is a continuous $\Theta:\mathbb{R}\to\mathbb{R}$ with $\Theta(t)-f(t)\in\mathbb{Z}$ for every $t$.
--
--   This turns an angle-type parameter that is only well defined modulo $1$ (for instance, the page of an open book through a moving point) into a continuous real-valued parameter.
--
--   **Formalization Note** $\mathbb{R}/\mathbb{Z}$ is `AddCircle (1 : ℝ)` and $f(t)\bmod1$ is the coercion `(f t : AddCircle (1 : ℝ))`; no continuity of $f$ itself is assumed.
-- source:
--   Standard lifting through the covering ℝ → ℝ/ℤ (e.g. Hatcher, Algebraic Topology, Prop. 1.30); used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Lemma 3.12

import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.Real.Lemmas

theorem HryniewiczCriterion.exists_continuous_lift_of_continuous_mod_one (f : ℝ → ℝ)
    (hf : Continuous (fun t => (f t : AddCircle (1 : ℝ)))) :
    ∃ Θ : ℝ → ℝ, Continuous Θ ∧ ∀ t, ∃ n : ℤ, Θ t = f t + n := by sorry
