-- Prove2me | Theorems.Thm_OAI_ArnoldCounterexample_Forms_normSq_fderiv
-- name    : OAI.ArnoldCounterexample.Forms.normSq_fderiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:20:24.966984+00:00
-- url     : https://prove2.me/theorems/9d219c86-e6a8-4366-978f-66f7709f316a
-- title:
--   The squared norm on $\mathbb{C}^n$ is the Hamiltonian of the circle action: $d|z|^2=-\omega(iz,\cdot)$
-- statement:
--   Let $n\in\mathbb{N}$. On $\mathbb{C}^n$, regarded as a real vector space, let $\omega_n(u,v)=2\sum_i\bigl(\operatorname{Re}u_i\operatorname{Im}v_i-\operatorname{Im}u_i\operatorname{Re}v_i\bigr)$ be the standard symplectic form and $|z|^2=\sum_i|z_i|^2$. Then for all $z,v\in\mathbb{C}^n$,
--   $$
--   d\bigl(|z|^2\bigr)[v]=-\,\omega_n(i z,\,v).
--   $$
--
--   So, up to sign, $|z|^2$ is the Hamiltonian generating the circle action $z\mapsto e^{i\theta}z$. This radial identity makes the restricted curvature forms basic on unit spheres.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Symplectic.lean#L86-L108

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped BigOperators ContDiff

theorem OAI.ArnoldCounterexample.Forms.normSq_fderiv (n : ℕ) (z v : CSpace n) :
    fderiv ℝ (normSq n) z v = -symplectic n (Complex.I • z) v := by sorry
