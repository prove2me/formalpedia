-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel
-- name    : LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/58665965-0ccc-56d8-a0f7-a059150b2ab5
-- title:
--   Derivative in x of the Bessel kernel k_ν
-- statement:
--   Fix a complex number $\nu$ and a real number $x$ with $0 < x$. For a complex parameter $\mu$ and a real argument $y$, the kernel `besselKernel` is defined as the Bochner integral over the open half-line $(0,\infty)$ of $t \mapsto e^{-(y(t+t^{-1})/2)} \, t^{\mu-1}$, the exponential factor being a real number coerced to $\mathbb{C}$ and the power being the complex `cpow` of the coerced variable $t$. The assertion is that the function $y \mapsto$ `besselKernel` $\nu\, y$, viewed as a map $\mathbb{R} \to \mathbb{C}$, has derivative at the point $x$ (in the sense of `HasDerivAt`, so in particular it is differentiable there) equal to $$-\bigl(k_{\nu-1}(x) + k_{\nu+1}(x)\bigr)/2,$$ where $k_{\nu\mp 1}(x)$ denotes the same integral with $\nu$ replaced by $\nu-1$ and by $\nu+1$ respectively. No restriction is imposed on $\nu$; positivity of $x$ is the only hypothesis.
--
--   This is the formal counterpart of the classical recurrence $K_\nu'(x) = -\tfrac12\bigl(K_{\nu-1}(x)+K_{\nu+1}(x)\bigr)$ for the modified Bessel function of the second kind, in the integral normalisation $k_\nu(x)=\int_0^\infty e^{-x(t+t^{-1})/2}t^{\nu-1}\,dt$. It feeds the simultaneous statement about $k_\nu$ and its derivative used in the archimedean Whittaker computations, where the functions $k_{\nu_0\pm 1/2}$ are re-expressed in terms of $k$ and $k'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel.lean

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x + besselKernel (ν + 1) x) / 2) x := by sorry
