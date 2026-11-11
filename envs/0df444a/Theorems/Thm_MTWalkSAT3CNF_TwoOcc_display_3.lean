-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_display_3
-- name    : MTWalkSAT3CNF.TwoOcc.display_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:45.878859+00:00
-- url     : https://prove2.me/theorems/eb9b3e3e-4c06-4d19-ae5e-5e7b09b98eca
-- title:
--   §3.2 display (3) — neighbour-weight identity for rooted trees
-- statement:
--   Let $T$ be a finite tree, $r$ a vertex of degree $d$ in $T$, and $W_T(v)=\sum_{w\in V(T)}2^{-d_T(v,w)}$. Then
--
--   $$\sum_{u\sim_T r}W_T(u)=\frac{d+3}{2}\,W_T(r)-\frac32 .$$
--
--   In the paper $r$ is the root of a defect tree; the identity is the first estimate behind the drift of $\Phi$.
--
--   Differences from the source:
--   - generalization: the root r of a defect tree T → any vertex r of any finite tree T (a SimpleGraph.IsTree on a finite type); reason: the derivation on p. 14 uses only that T is a finite tree; a defect tree is a tree with no parallel edges (e = q − 1), so it is an instance
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, display (3), p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc

/-- §3.2 display (3), p. 14, for every finite tree: if the vertex `r` has degree `d` in `T`, then
`Σ_{u ∼_T r} W_T(u) = ((d + 3)/2) W_T(r) − 3/2`. -/
theorem display_3 {W : Type*} [Fintype W] [DecidableEq W] (T : SimpleGraph W)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : W) :
    ∑ u ∈ T.neighborFinset r, treeWeight T u =
      ((T.degree r + 3 : ℝ) / 2) * treeWeight T r - 3 / 2 := by sorry

end MTWalkSAT3CNF.TwoOcc
