-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_lemma_4_3
-- name    : FracColorLocal.KrFree.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:23.233827+00:00
-- url     : https://prove2.me/theorems/e713d44d-c040-4f92-8f79-af06f931cf36
-- title:
--   Lemma 4.3 — deletion identity Σ_x w(x)g_x = (1−c)S − 6cT_G(w) − cΣ_v ζ_v(w(v)Λ_v − ξ_v/2)
-- statement:
--   Let $G$ be any finite graph, $u>0$ an objective weight, $0<c\le1$, and $w$ a positive vertex weight (no optimality assumption). With $\Lambda_v=w(N(v))$, $S=\sum_vu(v)w(v)$, $T_G(w)=\sum_{\{x,y,z\}}w(x)w(y)w(z)$ over unordered triangles, $\xi_v=\xi_{u(v)}(w(v))$, $\zeta_v=U'_{u(v)}(w(v))-2\Lambda_v$, and the gains $g_x=u(x)+c\,U_{G_x,u}(w)-c\,U_{G,u}(w)$ with $G_x=G-N[x]$,
--
--   $$\sum_xw(x)g_x=(1-c)S-6c\,T_G(w)-c\sum_v\zeta_v\big(w(v)\Lambda_v-\xi_v/2\big).$$
--
--   The identity reduces the induction step of Theorem 1.7 to bounding the weighted triangle count: when all $\zeta_v=0$, some vertex has $g_x\ge0$ as soon as $6cT_G(w)\le(1-c)S$.
--
--   Differences from the source:
--   - encoding: $U_{G_x,u}(w)$ on the induced subgraph $G-N[x]$ → the potential of $G$ restricted to the vertex set $V\setminus N[x]$ (`potentialOn`); reason: §1.5 restricts weights to an induced subgraph without renaming them; the two quantities are the same sum.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 19 (PDF 20), Lemma 4.3 (setting of §4.2, p. 18: u > 0, 0 < c ≤ 1)

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_FracColorLocal_KrFree_Potential

open OAI.CliqueFreeIndependence.WeightedGraph

namespace FracColorLocal.KrFree

/-- Lemma 4.3 (deletion identity): for every positive `w` and `0 < c ≤ 1`,
`∑_x w(x) g_x = (1 - c) S - 6 c T_G(w) - c ∑_v ζ_v (w(v) Λ_v - ξ_v / 2)`. -/
theorem lemma_4_3 {V : Type*} [Fintype V] (G : SimpleGraph V) (u w : V → ℝ) (c : ℝ)
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∑ x, w x * gain G u w c x =
      (1 - c) * sObj u w - 6 * c * triangleMass G w -
        c * ∑ v, zetaV G u w v * (w v * neighborMass G w v - xiV u w v / 2) := by sorry

end FracColorLocal.KrFree
