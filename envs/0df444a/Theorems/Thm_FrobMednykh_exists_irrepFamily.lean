-- Prove2me | Theorems.Thm_FrobMednykh_exists_irrepFamily
-- name    : FrobMednykh.exists_irrepFamily
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:14:29.36399+00:00
-- url     : https://prove2.me/theorems/8eef6fe1-e08d-409c-bb04-9e4cc79af68a
-- title:
--   Existence of a finite complete family of irreducible representations
-- statement:
--   $G$ is a finite group; representations are finite-dimensional over $\mathbb C$ (`FDRep ℂ G`), $\chi_V$ is the character and $d_V=\dim V$. An `IrrepFamily G ι` is a family $(V_i)_{i\in\iota}$ of irreducible representations, pairwise non-isomorphic, such that every irreducible representation is isomorphic to some $V_i$; $d_i=\dim V_i$, $\chi_i=\chi_{V_i}$. For every finite group $G$ there is a finite type $\iota$ and an `IrrepFamily G ι`.
-- source:
--   J.-P. Serre, Linear Representations of Finite Groups (Springer GTM 42, 1977), §2.4 (Corollary 2) and §2.5; N. Snyder, Mednykh's formula via lattice topological quantum field theories, arXiv:math/0703073 (2007), https://arxiv.org/abs/math/0703073, §3 (the set Ĝ)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem exists_irrepFamily (G : Type) [Group G] [Fintype G] :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (IrrepFamily G ι) := by sorry

end FrobMednykh
