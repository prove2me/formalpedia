-- Prove2me | Theorems.Thm_MathieuM23_m23_self_normalizing
-- name    : MathieuM23.m23_self_normalizing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T00:15:48.387768+00:00
-- url     : https://prove2.me/theorems/407419de-f1f9-45b4-93eb-cabe4bd08f31
-- title:
--   Corollary 3.6 (group-theoretic step) — $M_{23}$ is not normal in any larger subgroup of $S_{23}$
-- statement:
--   If $H$ is a subgroup of $S_{23}$ with $M_{23}\le H$ and $M_{23}\trianglelefteq H$, then $H=M_{23}$. Equivalently, $M_{23}$ is self-normalizing in $S_{23}$:
--
--   $$N_{S_{23}}(M_{23})=M_{23}.$$
--
--   This is the group-theoretic input that upgrades $G_{\mathrm{geom}}=M_{23}$ to $G_{\mathrm{arith}}=M_{23}$ in Corollary 3.6.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 7, proof of Corollary 3.6 ("$M_{23}$ is not normal in any larger subgroup of $S_{23}$")

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem m23_self_normalizing (H : Subgroup (Equiv.Perm (Fin 23))) (hle : M23 ≤ H)
    (hnormal : (M23.subgroupOf H).Normal) : H = M23 := by sorry

end MathieuM23
