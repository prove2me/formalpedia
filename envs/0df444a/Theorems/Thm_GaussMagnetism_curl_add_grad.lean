-- Prove2me | Theorems.Thm_GaussMagnetism_curl_add_grad
-- name    : GaussMagnetism.curl_add_grad
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T19:53:02.448446+00:00
-- url     : https://prove2.me/theorems/cc5cc116-9cfe-4928-b6b2-5e80db9183ee
-- title:
--   Gauge freedom: $\nabla\times(A+\nabla\varphi)=\nabla\times A$
-- statement:
--   Let $A:\mathbb R^3\to\mathbb R^3$ be a continuously differentiable vector field and $\varphi:\mathbb R^3\to\mathbb R$ a twice continuously differentiable scalar field. Then for every $x\in\mathbb R^3$,
--
--   $$\nabla\times(A+\nabla\varphi)(x)=\nabla\times A(x).$$
--
--   Consequently, if $A$ is a vector potential for a magnetic field $B$ (that is, $B=\nabla\times A$), then so is $A+\nabla\varphi$ for every such $\varphi$; this arbitrariness is called gauge freedom.
--
--   **Formalization Note** Regularity: $A$ is `ContDiff ℝ 1`, $\varphi$ is `ContDiff ℝ 2`.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 2, section 'Vector potential': the identity for A + ∇φ and the paragraph on gauge freedom.

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem curl_add_grad (A : Vec → Vec) (φ : Vec → ℝ) (hA : ContDiff ℝ 1 A)
    (hφ : ContDiff ℝ 2 φ) (x : Vec) :
    curl (fun y => A y + grad φ y) x = curl A x := by sorry

end GaussMagnetism
