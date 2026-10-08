-- Prove2me | Theorems.Thm_HryniewiczCriterion_winding_endpoint_profile
-- name    : HryniewiczCriterion.winding_endpoint_profile
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:23:35.276999+00:00
-- url     : https://prove2.me/theorems/2cbf34a0-448d-4a21-b2eb-5542b829cbf2
-- title:
--   Normalized winding profile and its angular derivative
-- statement:
--   Let $\varphi:[0,1]\to\mathrm{SL}(2,\mathbb R)$ be smooth and start at the identity. Put $v(s)=(\cos s,\sin s)$ and let $W(\varphi)$ be the set of normalized angular increments of the positive polar lifts initialized at $s\in[0,2\pi]$. There is a continuous function $\Delta:\mathbb R\to\mathbb R$ such that
--   $$W(\varphi)=\Delta([0,2\pi])=\Delta(\mathbb R).$$
--   For every $s\in\mathbb R$ there is a positive number $r$ with
--   $$\varphi(1)v(s)=r\,v(s+2\pi\Delta(s)),\qquad
--   \Delta'(s)=\frac{r^{-2}-1}{2\pi}.$$
--   The derivative is asserted at every real starting angle, including the angles representing the endpoints of the fundamental domain. This profile provides attained winding extrema and the derivative needed to detect fixed vectors at integer extrema.
--   **Formalization Note** The path is represented on all real times but is constrained only on $[0,1]$; the winding set uses continuous positive polar lifts on that interval.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, https://arxiv.org/abs/1105.2077, Section 2.1.1, pp. 5–6, angular description preceding Lemma 2.1 and its proof.

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped ContDiff

theorem HryniewiczCriterion.winding_endpoint_profile
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    ∃ Δ : ℝ → ℝ, Continuous Δ ∧
      windingInterval φ = Δ '' Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      windingInterval φ = Set.range Δ ∧
      ∀ s : ℝ, ∃ r : ℝ, 0 < r ∧
        (φ 1).mulVec (rotationVector s) =
          r • rotationVector (s + 2 * Real.pi * Δ s) ∧
        HasDerivAt Δ ((1 / r ^ 2 - 1) / (2 * Real.pi)) s := by sorry
