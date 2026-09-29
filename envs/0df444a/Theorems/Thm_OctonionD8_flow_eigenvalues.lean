-- Prove2me | Theorems.Thm_OctonionD8_flow_eigenvalues
-- name    : OctonionD8.flow_eigenvalues
-- status  : Proved
-- author  : @ShapeZero
-- created : 2026-09-27T05:27:29.733309+00:00
-- url     : https://prove2.me/theorems/3273ad56-04b9-4c14-83e9-bd8c88010ca6
-- title:
--   Corollary: the frequencies are $0$, $2$ and $2\sin(\theta/2)$
-- statement:
--   Let $0 < \theta < \pi$, and let $M$ be the flow matrix with $c = \cos\theta$, $s = \sin\theta$. Then the complex eigenvalues of $M$ (the roots of $\chi_M$ over $\mathbb{C}$, with multiplicity) are exactly
--
--   $$
--   0,\ 0,\ \pm 2i,\ \pm 2i\sin(\theta/2),\ \pm 2i\sin(\theta/2),
--   $$
--
--   and $0 < \sin(\theta/2) < 1$. So the two nonzero frequencies $2$ and $2\sin(\theta/2)$ are distinct, and their ratio is $1/\sin(\theta/2)$.
-- source:
--   Motivated by the two-generator D8 flow in the Shape Zero derivation (Shape Zero LLC): https://github.com/ShapeZeroSZ/shape-zero/blob/main/00_START_HERE/MODEL_SPEC.md §1b and https://github.com/ShapeZeroSZ/shape-zero/blob/main/02_synthesis/D8_SYNTHESIS.md ; Fano plane: Prove2Me definition RolesForceSeven.fano (mission "The role postulates force exactly seven points") ; public references: Wikipedia, "Octonion": https://en.wikipedia.org/wiki/Octonion ; Wikipedia, "Fano plane": https://en.wikipedia.org/wiki/Fano_plane

import Mathlib
import Definitions.Def_OctonionD8_flow

namespace OctonionD8

open Polynomial

theorem flow_eigenvalues (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < Real.pi) :
    ((flowMat (Real.cos θ) (Real.sin θ)).charpoly.map (algebraMap ℝ ℂ)).roots =
      {0, 0, 2 * Complex.I, -(2 * Complex.I),
        2 * Complex.I * (Real.sin (θ / 2) : ℂ), 2 * Complex.I * (Real.sin (θ / 2) : ℂ),
        -(2 * Complex.I * (Real.sin (θ / 2) : ℂ)), -(2 * Complex.I * (Real.sin (θ / 2) : ℂ))} ∧
      0 < Real.sin (θ / 2) ∧ Real.sin (θ / 2) < 1 := by
  sorry

end OctonionD8
