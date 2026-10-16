-- Prove2me | Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt
-- name    : OAI.ThreeManifold.Neck.pairing_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:14:28.85447+00:00
-- url     : https://prove2.me/theorems/52a94624-ebca-4de3-b608-7cc7c77deb78
-- title:
--   Product rule for the matrix pairing $u(r)^{\mathsf T}A(r)\,v(r)$
-- statement:
--   For a real $2\times 2$ matrix $A$ and $u,v\in\mathbb{R}^2$ write $\langle u,v\rangle_A = u^{\mathsf T}Av$. Let $A:\mathbb{R}\to\mathbb{R}^{2\times2}$ and $u,v:\mathbb{R}\to\mathbb{R}^2$, and let $s\in\mathbb{R}$. Suppose $A$, $u$, $v$ are differentiable at $s$ with derivatives $A'(s)=A'$, $u'(s)=u'$, $v'(s)=v'$. Then $r\mapsto\langle u(r),v(r)\rangle_{A(r)}$ is differentiable at $s$, with
--   $$
--   \frac{d}{dr}\Big|_{r=s}\langle u(r),v(r)\rangle_{A(r)}=\langle u',v(s)\rangle_{A(s)}+\langle u(s),v(s)\rangle_{A'}+\langle u(s),v'\rangle_{A(s)} .
--   $$
--
--   This is the three-factor Leibniz rule for a bilinear form with a varying matrix. It is the basic differentiation tool for the neck computations, where pairings against $\partial_tQ$ are differentiated along curves.
--
--   **Formalization Note** Differentiability of matrix- and vector-valued maps is with respect to the product (sup) norm, which is equivalent to entrywise differentiability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Neck.lean#L276-L293

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

open OAI OAI.ThreeManifold OAI.ThreeManifold.Neck
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

theorem OAI.ThreeManifold.Neck.pairing_hasDerivAt {A : ℝ → TMat} {u v : ℝ → TVec}
    {A' : TMat} {u' v' : TVec} {s : ℝ}
    (hA : HasDerivAt A A' s) (hu : HasDerivAt u u' s) (hv : HasDerivAt v v' s) :
    HasDerivAt (fun r => pairing (A r) (u r) (v r))
      (pairing (A s) u' (v s) + pairing A' (u s) (v s) +
        pairing (A s) (u s) v') s := by sorry
