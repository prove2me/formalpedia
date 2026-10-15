-- Prove2me | Theorems.Thm_OAI_TriangularCovering_d_le_max_endpoints
-- name    : OAI.TriangularCovering.d_le_max_endpoints
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:43:13.380532+00:00
-- url     : https://prove2.me/theorems/bab8e546-3cc9-479a-b9ec-6ad1f317ba81
-- title:
--   The quartic $d(q)=q^2(1+q^2)/16$ attains its maximum on an interval at an endpoint
-- statement:
--   Let $d:\mathbb{R}\to\mathbb{R}$ be the quartic polynomial
--   $$
--   d(q)=\frac{q^2(1+q^2)}{16}.
--   $$
--   For all real numbers $a,q,b$ with $a\le q\le b$,
--   $$
--   d(q)\le\max\{d(a),\,d(b)\}.
--   $$
--
--   Equivalently, on every closed interval $[a,b]$ the maximum of $d$ is attained at one of the two endpoints. In the covering of the tetrahedron by tilted triangular cylinders, $d$ enters the cutoff coefficient $M(a,b)=\eta+\max\{d(a),d(b)\}$ (with $\eta=1/1000$) of a mesh cell $[a,b]$; the lemma shows $M(a,b)\ge\eta+d(q)$ for every $q\in[a,b]$, so that $M(a,b)=\eta+\max_{[a,b]}d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L19-L38

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.d_le_max_endpoints {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    d q ≤ max (d a) (d b) := by sorry
