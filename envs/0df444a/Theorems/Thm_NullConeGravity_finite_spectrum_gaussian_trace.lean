-- Prove2me | Theorems.Thm_NullConeGravity_finite_spectrum_gaussian_trace
-- name    : NullConeGravity.finite_spectrum_gaussian_trace
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:46:11.233133+00:00
-- url     : https://prove2.me/theorems/3de10802-1378-47dd-82a7-e768071584be
-- title:
--   Finite-spectrum Gaussian trace identity (Eq. 5.66)
-- statement:
--   Let $C$ be a complex preparation matrix between finite-dimensional spaces. In an area eigenbasis with eigenvalues $s_i\ge 0$, write $t=s_b$ for the positive window center and set
--   $$f_t(s)=\exp\!\left(-\frac{(s-t)^2}{4t}\right),\qquad C_t=C\,\operatorname{diag}\!\left(\sqrt{f_t(s_i)}\right).$$
--
--   Integrating the windowed traces recovers the full trace.
--   $$\operatorname{Tr}(C^\dagger C)=\int_0^\infty \frac{\operatorname{Tr}(C_t^\dagger C_t)}{\sqrt{4\pi t}}\,dt.$$
--
--   This is the finite-spectrum version of the second equality in Eq. (5.66), with $Z(\ell)=\operatorname{Tr}(C^\dagger C)$ in the finite model. The eigenvalues may repeat and may include zero.
-- source:
--   Venkatesa Chandrasekaran, An algebraic quantization of gravity from the null cone, arXiv:2611.34924v1, §5.3, second equality of Eq. (5.66). The Gaussian-filtered preparation is defined in §5.2, Eq. (5.25). https://arxiv.org/html/2611.34924v1#S5.E66

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set MeasureTheory

namespace NullConeGravity
theorem finite_spectrum_gaussian_trace {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (C : Matrix κ ι ℂ) :
    let Cb (t : ℝ) := C * Matrix.diagonal (fun i =>
      (Real.sqrt (Real.exp (-((s i - t) ^ 2) / (4 * t))) : ℂ))
    Matrix.trace (C.conjTranspose * C) =
      ∫ t in Ioi (0 : ℝ), Matrix.trace ((Cb t).conjTranspose * Cb t) /
        (Real.sqrt (4 * Real.pi * t) : ℂ) := by sorry
end NullConeGravity
