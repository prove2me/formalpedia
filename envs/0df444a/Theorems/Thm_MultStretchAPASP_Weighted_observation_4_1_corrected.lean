-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_4_1_corrected
-- name    : MultStretchAPASP.Weighted.observation_4_1_corrected
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:25:01.81465+00:00
-- url     : https://prove2.me/theorems/39341f11-fe5d-4e9c-a180-e905721e5376
-- title:
--   Observation 4.1, corrected: the result of Algorithm 5 includes δ_H(u, v) and the update from source v (corrected: missing terms)
-- statement:
--   **Source** (Observation 4.1, p. 14): for a weighted undirected graph $H$, a set $S$ of sources and a symmetric table $d$, the table $d_{\mathrm{end}}$ after Algorithm 5 satisfies, for every $(u, v) \in (S \times V_H) \cup (V_H \times S)$, $d_{\mathrm{end}}[u, v] = \min(d[u, v], \min_{w \in V_H} d[u, w] + \delta_H(w, v))$.
--
--   **Variant:** for every pair $(u, v)$, $d_{\mathrm{end}}[u, v]$ is the minimum of $d[u, v]$, of $\min(\delta_H(u, v), \min_w d[u, w] + \delta_H(w, v))$ when $u \in S$, and of $\min(\delta_H(v, u), \min_w d[v, w] + \delta_H(w, u))$ when $v \in S$.
--
--   **Difference:** the variant adds the walks of the star-augmented graph that use no star edge ($\delta_H$) and the symmetric update made by the source $v$, which the printed formula omits.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 14, Observation 4.1 (corrected)

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Alg10

set_option autoImplicit false

open scoped ENNReal

namespace MultStretchAPASP.Weighted

theorem observation_4_1_corrected {n : ℕ} (H : WMat n) (hH : IsWGraph H) (S : Finset (Fin n))
    (d : Table n) (hd : ∀ x y : Fin n, d x y = d y x) (u v : Fin n) :
    alg5 H S d u v = min (d u v)
      (min (if u ∈ S then min (dist H u v) (⨅ x : Fin n, d u x + dist H x v) else ⊤)
        (if v ∈ S then min (dist H v u) (⨅ x : Fin n, d v x + dist H x u) else ⊤)) := by sorry

end MultStretchAPASP.Weighted
