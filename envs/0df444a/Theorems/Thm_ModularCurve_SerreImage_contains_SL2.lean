-- Prove2me | Theorems.Thm_ModularCurve_SerreImage_contains_SL2
-- name    : ModularCurve.SerreImage.contains_SL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/a7efc83e-98c1-5f88-82d9-0a806c7b2e31
-- title:
--   Irreducible subgroups with a unipotent element contain SL₂(𝔽ₚ)
-- statement:
--   Let $p$ be a prime and let $H$ be a subgroup of $\mathrm{GL}_2(\mathbb{Z}/p)$, the general linear group of $2\times 2$ matrices indexed by `Fin 2` over $\mathbb{Z}/p$. Two hypotheses are imposed. First, an irreducibility condition in the form: for every vector $v \colon \mathrm{Fin}\,2 \to \mathbb{Z}/p$ with $v \neq 0$ there is an element $g \in H$ such that the matrix underlying $g$, applied to $v$ by `mulVec`, is different from $c \cdot v$ for every scalar $c \in \mathbb{Z}/p$; that is, no nonzero vector has its line stabilised by all of $H$, witnessed elementwise. Second, a unipotence condition: there exists $u \in H$ whose underlying matrix satisfies $(u - 1)^2 = 0$ and which is not the identity element of the group. The conclusion is that the range of the homomorphism `Matrix.SpecialLinearGroup.toGL` from $\mathrm{SL}_2(\mathbb{Z}/p)$ to $\mathrm{GL}_2(\mathbb{Z}/p)$ is contained in $H$ as subgroups, i.e. $H$ contains the image of $\mathrm{SL}_2(\mathbb{F}_p)$ inside $\mathrm{GL}_2(\mathbb{F}_p)$.
--
--   This is the group-theoretic core of Serre's "big image" statement for two-dimensional mod $p$ representations: an irreducible subgroup of $\mathrm{GL}_2(\mathbb{F}_p)$ containing a nontrivial unipotent element already contains $\mathrm{SL}_2(\mathbb{F}_p)$. The proof uses the fact that the elementary matrices generate $\mathrm{SL}_2(\mathbb{Z}/N)$, in the form [`ModularCurve.closure_elemSet_eq_top`](thm.html#ModularCurve.closure_elemSet_eq_top), and the result feeds into the counting estimate [`Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le`](thm.html#Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean

import Definitions.Def_ModularCurve_SL2Elementary
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix MatrixGroups Subgroup

theorem ModularCurve.SerreImage.contains_SL2 {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H := by sorry
