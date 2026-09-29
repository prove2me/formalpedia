-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
-- name    : Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/db00cc59-3fde-598b-97f0-17fc2e0a736f
-- title:
--   Subgroups of GL₂(𝔽₃) of order ≤ 24 with full determinant
-- statement:
--   Let $H$ be a subgroup of the general linear group $\mathrm{GL}_2(\mathbb{Z}/3)$ of invertible $2\times 2$ matrices over $\mathbb{Z}/3$, subject to three hypotheses. First, $H$ stabilises no line: there is no vector $v \in (\mathbb{Z}/3)^2$ with $v \neq 0$ such that for every $h \in H$ there exists a scalar $c \in \mathbb{Z}/3$ with $h v = c\,v$, the product being the matrix–vector product of the underlying matrix of $h$ with $v$. Secondly, the determinant is surjective on $H$: for every unit $d \in (\mathbb{Z}/3)^{\times}$ there is an $h \in H$ with $\det h = d$. Thirdly, the cardinality of $H$ (as a natural number, via `Nat.card`) is at most $24$. The conclusion is that $\operatorname{card} H$ divides $16$. Since $\mathrm{GL}_2(\mathbb{Z}/3)$ has order $48$, the third hypothesis says exactly that $H$ is a proper subgroup; the conclusion in particular forces the order of $H$ to be a power of $2$ dividing $16$, so no such $H$ has order divisible by $3$.
--
--   This is the group-theoretic half of Serre's classification of subgroups of $\mathrm{GL}_2(\mathbb{F}_p)$ specialised to $p = 3$: a proper subgroup with full determinant acting without a stable line is contained in the normaliser of a split or non-split Cartan subgroup, of order $8$ or $16$. It is used to rule out small images in the mod $3$ representation, feeding into [`GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar`](thm.html#GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d)
    (hle : Nat.card H ≤ 24) :
    Nat.card H ∣ 16 := by sorry
