-- Prove2me | Theorems.Thm_MathieuM23_triple_mem_sigmaC
-- name    : MathieuM23.triple_mem_sigmaC
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:36:13.573737+00:00
-- url     : https://prove2.me/theorems/995d0b5d-18dd-4c57-bd11-05063865dd76
-- title:
--   §3 — $(g_1,g_2,g_3)\in\Sigma_c$ for $c=(2,23A,23B)$
-- statement:
--   The explicit triple $(g_1,g_2,g_3)$ represents a point of the Nielsen class for the classes $(2,23A,23B)$:
--
--   1. $(g_1,g_2,g_3)\in\Sigma_c$, i.e. $g_1g_2g_3=1$, $\langle g_1,g_2,g_3\rangle=M_{23}$ (in particular $g_3\in M_{23}$), and each $g_i$ lies in its own class;
--   2. $g_2$ and $g_3$ are **not** conjugate in $M_{23}$, so the two classes of elements of order $23$ ($23A$ and $23B$) are distinct;
--   3. $g_1$ has order $2$ and $g_2,g_3$ have order $23$.
--
--   **Formalization Note** The classes $C_1,C_2,C_3$ are defined as the $M_{23}$-classes of $g_1,g_2,g_3$, so the substantive content is the product relation, generation, the orders, and the non-conjugacy of $g_2$ and $g_3$.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4–5, §3 ("We have $(g_1,g_2,g_3)\in\Sigma_c$") together with the class labels $2, 23A, 23B$

import Definitions.Def_MathieuM23_Nielsen

namespace MathieuM23

theorem triple_mem_sigmaC :
    (g₁, g₂, g₃) ∈ sigmaC ∧ g₃ ∉ classIn g₂ ∧
      orderOf g₁ = 2 ∧ orderOf g₂ = 23 ∧ orderOf g₃ = 23 := by sorry

end MathieuM23
