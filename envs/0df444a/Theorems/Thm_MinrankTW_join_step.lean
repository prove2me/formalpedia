-- Prove2me | Theorems.Thm_MinrankTW_join_step
-- name    : MinrankTW.join_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:06.73633+00:00
-- url     : https://prove2.me/theorems/25270678-aadf-4663-b288-c26b06bec0cc
-- title:
--   Section 3.2 — the join step: $R(M_u+M_v)=R(M_u)\boxplus R(M_v)$ and interior ranks add
-- statement:
--   At a join node with children $u,v$ sharing the bag $(B_r,B_c)$, let $M_u,M_v$ be the children's partial matrices with interiors $(I_{u,r},I_{u,c})$ and $(I_{v,r},I_{v,c})$. Assume the children's forgotten vertices are disjoint and disjoint from the bag, that no support edge connects them ($M_u$ vanishes on the rows and columns of $I_v$ and $M_v$ on those of $I_u$), and that every entry is introduced in exactly one child (the entry sets $\Omega_u,\Omega_v$ are disjoint and $M_u$, $M_v$ vanish off them). Then for $M_t=M_u+M_v$ with interior $I_u\cup I_v$:
--
--   1. $M_t$ determines each child matrix by restriction to its introduced positions;
--   2. the new linear relation is $R(M_u)\boxplus R(M_v)$;
--   3. the interior ranks add: $\operatorname{rank}M_t[I_t,I_t]=\operatorname{rank}M_u[I_u,I_u]+\operatorname{rank}M_v[I_v,I_v]$.
--
--   Differences from the source:
--   - encoding: bag and interior coordinates of a bag with a columns and c rows (F^a ⊕ F^c) → ambient coordinates in F^n × F^m supported on the bag (interior and bag disjoint); reason: the same relation with the bag coordinates embedded; same instances
--   - encoding: the separation properties of a nice decomposition at a join → explicit hypotheses: disjoint interiors, interiors disjoint from the bag, vanishing of each child matrix on the other child's interior rows and columns, disjoint introduced-entry sets; reason: these are the decomposition axioms the paragraph invokes; same instances
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, p.11, the join step

import Mathlib
import Definitions.Def_MinrankTW_relJoin
import Definitions.Def_MinrankTW_relOfPartial
import Definitions.Def_MinrankTW_interiorRank

namespace MinrankTW

/-- **Section 3.2, the join step**, Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.11. Let `M_u`, `M_v` be the partial matrices of
the two children of a join, with the same bag `(B_r, B_c)` and interiors `(I_{u,r}, I_{u,c})`,
`(I_{v,r}, I_{v,c})`: the children's forgotten vertices are disjoint, disjoint from the bag, and no
support edge connects them (`M_u` vanishes on the rows and columns of `I_v`, and `M_v` on those of
`I_u`); every entry is introduced in exactly one child (`M_u`, `M_v` vanish off the disjoint
introduced-entry sets `Ω_u`, `Ω_v`). Then for `M_t = M_u + M_v` with interior `I_u ∪ I_v`:
`M_t` determines each child matrix by restriction to its introduced positions, the new linear
relation is `R(M_u) ⊞ R(M_v)` (Eq. (7)), and the interior ranks add. -/
theorem join_step {F : Type} [Field F] [Fintype F] {m n : ℕ} (Mu Mv : Matrix (Fin m) (Fin n) F)
    (Iur Ivr Br : Finset (Fin m)) (Iuc Ivc Bc : Finset (Fin n))
    (hr : Disjoint Iur Ivr) (hc : Disjoint Iuc Ivc)
    (hrB : Disjoint (Iur ∪ Ivr) Br) (hcB : Disjoint (Iuc ∪ Ivc) Bc)
    (hu : ∀ i j, (i ∈ Ivr ∨ j ∈ Ivc) → Mu i j = 0)
    (hv : ∀ i j, (i ∈ Iur ∨ j ∈ Iuc) → Mv i j = 0)
    (Ωu Ωv : Finset (Fin m × Fin n)) (hΩ : Disjoint Ωu Ωv)
    (hΩu : ∀ i j, (i, j) ∉ Ωu → Mu i j = 0) (hΩv : ∀ i j, (i, j) ∉ Ωv → Mv i j = 0) :
    (∀ i j, Mu i j = (if (i, j) ∈ Ωu then (Mu + Mv) i j else 0) ∧
      Mv i j = (if (i, j) ∈ Ωv then (Mu + Mv) i j else 0)) ∧
    relOfPartial (Mu + Mv) (Iur ∪ Ivr) Br (Iuc ∪ Ivc) Bc =
      relJoin (relOfPartial Mu Iur Br Iuc Bc) (relOfPartial Mv Ivr Br Ivc Bc) ∧
    interiorRank (Mu + Mv) (Iur ∪ Ivr) (Iuc ∪ Ivc) =
      interiorRank Mu Iur Iuc + interiorRank Mv Ivr Ivc := by sorry

end MinrankTW
