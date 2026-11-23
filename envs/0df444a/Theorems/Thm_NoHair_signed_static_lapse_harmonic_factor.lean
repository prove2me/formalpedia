-- Prove2me | Theorems.Thm_NoHair_signed_static_lapse_harmonic_factor
-- name    : NoHair.signed_static_lapse_harmonic_factor
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:18:01.544403+00:00
-- url     : https://prove2.me/theorems/5caca4bd-0b77-4a09-8506-15a104ffe74e
-- title:
--   Harmonicity of the conformal factor across a static horizon
-- statement:
--   In Euclidean coordinates on a three-dimensional conformal double, let the signed static lapse $V$ be $C^2$ off the compactification point and satisfy $V>-1$. Write $U=2/(1+V)$. On each side $V\ne0$ assume the static lapse equation $\operatorname{div}(U^2\nabla V)=0$, which is $\Delta_{U^4\delta}V=0$ in divergence form. Then $U$ is harmonic throughout the punctured double, including the entire zero-lapse level. No differential equation is prescribed on the zero level.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, section 2, equations (2.1)–(2.4), and proof of Theorem 1.1 in section 5, equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326. Elementary coordinate consequence of (5.4) and (5.6) on each copy, with the sign of the lapse reversed on the second copy.

import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set InnerProductSpace

theorem NoHair.signed_static_lapse_harmonic_factor (V : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hreg : ContDiffOn ℝ 2 V ({0}ᶜ)) (hlower : ∀ x, x ≠ 0 → -1 < V x)
    (hflux : ∀ x : EuclideanSpace ℝ (Fin 3), x ≠ 0 → V x ≠ 0 →
        ∑ i : Fin 3, fderiv ℝ
          (fun y => (2 / (1 + V y))^2 * fderiv ℝ V y (EuclideanSpace.single i (1:ℝ)))
          x (EuclideanSpace.single i (1:ℝ)) = 0) :
    HarmonicOnNhd (fun x => 2 / (1 + V x)) ({0}ᶜ) := by sorry
