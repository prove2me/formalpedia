-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_cospherical_transport
-- name    : OAI.EuclideanRamsey.cospherical_transport
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:23:34.745837+00:00
-- url     : https://prove2.me/theorems/21a63eea-dda1-4755-817b-e2ee05655f90
-- title:
--   Congruence to a full-dimensional spherical configuration transfers sphericity
-- statement:
--   Let $a_0,\dots,a_{s-1}\in\mathbb R^D$ and $b_0,\dots,b_{s-1}\in\mathbb R^d$. Suppose the $b_i$ affinely span $\mathbb R^d$ and are congruent to the $a_i$, that is, $|a_i-a_j|=|b_i-b_j|$ for all $i,j$. If the $b_i$ lie on a sphere with centre $c$ and radius $\rho$, then
--   $$
--   |a_i-c'|=\rho\qquad\text{for all }i,\ \text{for some }c'\in\mathbb R^D .
--   $$
--
--   So sphericity can be checked on a representative of the configuration in the dimension of its affine span.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SphereTransport.lean#L10-L40

import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical

open OAI OAI.EuclideanRamsey

theorem OAI.EuclideanRamsey.cospherical_transport {s D d : ℕ}
    (a : Fin s → Space D) (b : Fin s → Space d)
    (hspan : affineSpan ℝ (Set.range b) = ⊤)
    (hab : Congruent a b)
    (hb : EuclideanGeometry.Cospherical (Set.range b)) :
    EuclideanGeometry.Cospherical (Set.range a) := by sorry
