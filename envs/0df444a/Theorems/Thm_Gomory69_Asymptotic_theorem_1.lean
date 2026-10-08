-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_theorem_1
-- name    : Gomory69.Asymptotic.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:47:04.401833+00:00
-- url     : https://prove2.me/theorems/25f1eec2-64a0-4638-a88a-3e91a3afc5fb
-- title:
--   THEOREM 1, p. 459 — an irreducible t satisfies ∏(1 + t(g)) ≤ |G|
-- statement:
--   Let $\mathcal G$ be a finite Abelian group and $\mathcal N$ a set of nonzero elements of $\mathcal G$. If the nonnegative integer vector $t=(t(g))_{g\in\mathcal N}$ is irreducible, then
--
--   $$\prod_{g\in\mathcal N}\bigl(1+t(g)\bigr)\le|\mathcal G|,$$
--
--   where $|\mathcal G|$ is the number of elements of the group.
--
--   The bound limits the size of every irreducible point, and hence (by THEOREM 2) of every vertex of $P(\mathcal G,\mathcal N,g_0)$; it is the source of the bound $l_{\max}(D-1)$ in THEOREM 4.
--
--   **Formalization Note** The vector $t$ need not solve the group equation. $0\notin\mathcal N$ is the paper's $\mathcal N\subseteq\mathcal G^+$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 459, THEOREM 1

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron

namespace Gomory69.Asymptotic

/-- THEOREM 1 (p. 459): an irreducible nonnegative integer vector `t` on a set `𝒩` of
nonzero elements of a finite Abelian group `𝒢` satisfies `∏_{g ∈ 𝒩} (1 + t(g)) ≤ |𝒢|`. -/
theorem theorem_1 {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by sorry

end Gomory69.Asymptotic
