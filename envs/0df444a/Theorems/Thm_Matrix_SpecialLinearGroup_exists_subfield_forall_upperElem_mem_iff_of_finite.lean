-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite
-- name    : Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/81d975b0-0b0f-5da0-b70d-a0c5ece878b1
-- title:
--   Dickson's theorem, root-group form, in odd characteristic
-- statement:
--   Let $K$ be a field of characteristic $p$ with $p$ prime and $p \neq 2$, and let $G$ be a finite subgroup of $\mathrm{SL}_2(K)$. Write $u(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ for the upper unipotent matrix with parameter $t$ (the element [`ModularCurve.upperElem t`](def/ModularCurve_SL2Elementary.html#L16)) and $l(t) = \begin{pmatrix} 1 & 0 \\ t & 1\end{pmatrix}$ for the lower one ([`ModularCurve.lowerElem t`](def/ModularCurve_SL2Elementary.html#L19)). Assume $u(1) \in G$ and that $l(\mu) \in G$ for some $\mu \neq 0$. Then one of the following two alternatives holds: either $p = 3$ and every $t \in K$ with $u(t) \in G$ satisfies $t^3 = t$ (that is, the parameters of the upper unipotent elements of $G$ lie in $\mathbb{F}_3$); or there is a subfield $F$ of $K$ which is finite and such that, for every $t \in K$, $u(t) \in G$ if and only if $t \in F$, and likewise $l(t) \in G$ if and only if $t \in F$. In particular, in the second case the two parameter sets coincide with one and the same finite subfield of $K$.
--
--   This is the portion of Dickson's classification of the finite subgroups of $\mathrm{SL}_2$ over a field of characteristic $p$ that applies when there is more than one Sylow $p$-subgroup: the parameters of the transvections in $G$ fixing either basis vector form a finite subfield, apart from an exceptional configuration in characteristic $3$. It is used to produce a finite subfield $F$ with a conjugate of $\mathrm{SL}_2(F)$ inside the given group, in [`Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card`](thm.html#Matrix.GeneralLinearGroup.exists_subfield_specialLinearGroup_conj_le_of_dvd_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_exists_subfield_forall_upperElem_mem_iff_of_finite.lean

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G]
    (hU : ModularCurve.upperElem (1 : K) ∈ G)
    (hL : ∃ μ : K, μ ≠ 0 ∧ ModularCurve.lowerElem μ ∈ G) :
    (p = 3 ∧ ∀ t : K, ModularCurve.upperElem t ∈ G → t ^ 3 = t) ∨
    ∃ F : Subfield K, Finite F ∧
      (∀ t : K, ModularCurve.upperElem t ∈ G ↔ t ∈ F) ∧
      (∀ t : K, ModularCurve.lowerElem t ∈ G ↔ t ∈ F) := by sorry
