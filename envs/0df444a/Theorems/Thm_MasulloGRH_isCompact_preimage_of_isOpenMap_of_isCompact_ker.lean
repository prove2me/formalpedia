-- Prove2me | Theorems.Thm_MasulloGRH_isCompact_preimage_of_isOpenMap_of_isCompact_ker
-- name    : MasulloGRH.isCompact_preimage_of_isOpenMap_of_isCompact_ker
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:18:19.761144+00:00
-- url     : https://prove2.me/theorems/37f91d3f-3d4d-4e4a-a4ca-a71529b3c877
-- title:
--   A continuous open homomorphism with compact kernel from a locally compact group is proper
-- statement:
--   Let $G$ be a locally compact topological group, $H$ a Hausdorff topological group, and $f:G\to H$ a continuous open homomorphism with compact kernel. Then $f$ is proper: for every compact $K\subseteq H$, the preimage $f^{-1}(K)$ is compact.
--
--   Proof: choose a compact neighbourhood $V_0$ of $1$ in $G$. Then $f(V_0)$ is a neighbourhood of $1$ and $f(G)$ is an open, hence closed, subgroup. Cover the compact set $K\cap f(G)$ by finitely many translates $f(p_j)f(V_0)$. Then
--   $$f^{-1}(K)\subseteq\bigcup_j p_j\,V_0\ker f,$$
--   which is compact, and $f^{-1}(K)$ is closed.
--
--   In Masullo's Appendix D this is used for the presentations $\pi:\Gamma\to\Gamma/k\cong\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$ (compact kernel $k$). It shows that the graph of a correspondence $p\mapsto(\alpha(p),\beta(p))$ between elementary groups is closed and has polynomially controlled growth.
-- source:
--   Standard (e.g. Bourbaki, General Topology III §4); used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.1.5

import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

namespace MasulloGRH

theorem isCompact_preimage_of_isOpenMap_of_isCompact_ker
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →* H) (hc : Continuous f) (ho : IsOpenMap f) (hk : IsCompact {x : G | f x = 1})
    {K : Set H} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  sorry

end MasulloGRH
