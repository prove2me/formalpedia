-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_4_1
-- name    : MultStretchAPASP.Weighted.observation_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:44.026074+00:00
-- url     : https://prove2.me/theorems/53187a52-14c1-4c2f-941b-9620c47b4e19
-- title:
--   Observation 4.1 — the result of Algorithm 5: d_end[u, v] = min(d[u, v], min_w d[u, w] + δ_H(w, v)) on (S × V_H) ∪ (V_H × S)
-- statement:
--   Let $H=(V_H,E_H,w)$ be a weighted undirected graph on $n$ vertices, $S\subseteq V_H$ a set of sources and $d$ a symmetric table of distance estimates with values in $[0,\infty]$. Algorithm 5 ($\textsc{Estimate\_augmented\_MSSP}(H,S,d)$) computes, for each source $u\in S$, the distances $\delta_{H_u}(u,\cdot)$ in $H$ augmented by the star at $u$ whose edge $(u,v)$ has weight $d[u,v]$, and then lowers $d[u,v]$ and $d[v,u]$ to $\delta_{H_u}(u,v)$ for all $(u,v)\in S\times V_H$. Let $d_{\mathrm{end}}$ be the table at the end. Then for every pair $(u,v)$ with $u\in S$ or $v\in S$,
--   $$d_{\mathrm{end}}[u,v]=\min\Bigl(d[u,v],\ \min_{w\in V_H}\bigl(d[u,w]+\delta_H(w,v)\bigr)\Bigr).$$
--
--   The observation is the paper's description of what one call of Algorithm 5 does; Lemmas 4.2 and 5.4 use it to show that the call never underestimates a distance.
--
--   **Formalization Note.** The statement is formalized as printed (see the mission's findings: the equality omits the walks of $H_u$ that use no star edge).
--
--   Differences from the source:
--
--   - encoding: an undirected graph G = (V, E, w) with w : E → ℝ≥0 → a symmetric weight matrix w : Fin n → Fin n → ℝ≥0∞ with ⊤ on the diagonal (IsWGraph), w x y = ⊤ meaning no edge; distances δ in ℝ≥0∞ (⊤ for disconnected pairs); reason: same graphs; ℝ≥0∞ represents the paper's ∞ exactly, so no junk value arises for disconnected pairs
--   - encoding: a table d[·, ·] storing symmetric distance estimates → d : Fin n → Fin n → ℝ≥0∞ with d x y = d y x for all x, y; reason: Algorithm 5's input specification; estimates may be ∞
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 14, Observation 4.1

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Alg10

set_option autoImplicit false

open scoped ENNReal

namespace MultStretchAPASP.Weighted

/-- **Observation 4.1** (p. 14), as printed. For a weighted undirected graph `H` on `Fin n`, a set
`S` of sources and a symmetric table `d`, let `d_end = alg5 H S d` be the table after
Algorithm 5. Then for every pair `(u, v)` with `u ∈ S` or `v ∈ S`,
`d_end[u, v] = min(d[u, v], min_{w ∈ V_H} (d[u, w] + δ_H(w, v)))`. -/
theorem observation_4_1 {n : ℕ} (H : WMat n) (hH : IsWGraph H) (S : Finset (Fin n))
    (d : Table n) (hd : ∀ x y : Fin n, d x y = d y x) (u v : Fin n) (huv : u ∈ S ∨ v ∈ S) :
    alg5 H S d u v = min (d u v) (⨅ x : Fin n, d u x + dist H x v) := by sorry

end MultStretchAPASP.Weighted
