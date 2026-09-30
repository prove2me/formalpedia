-- Prove2me | Theorems.Thm_GaussMagnetism_curl_grad_eq_zero
-- name    : GaussMagnetism.curl_grad_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T19:12:15.489805+00:00
-- url     : https://prove2.me/theorems/3bbaa545-04b0-45bc-a1ae-040df53073fe
-- title:
--   The curl of a gradient vanishes: $\nabla\times(\nabla\varphi)=0$
-- statement:
--   Let $\varphi:\mathbb R^3\to\mathbb R$ be a twice continuously differentiable scalar field. Then for every $x\in\mathbb R^3$,
--
--   $$\nabla\times(\nabla\varphi)(x)=0.$$
--
--   This identity is what makes the magnetic vector potential non-unique: adding a gradient to a vector potential does not change its curl (gauge freedom).
--
--   **Formalization Note** $C^2$ regularity is stated as `ContDiff ℝ 2 φ`; `grad` is `TongEM.grad` and `curl` is `Larmor.curl`.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 2, section 'Vector potential': 'since the curl of a gradient is the zero vector field'.

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem curl_grad_eq_zero (φ : Vec → ℝ) (hφ : ContDiff ℝ 2 φ) (x : Vec) :
    curl (grad φ) x = 0 := by sorry

end GaussMagnetism
