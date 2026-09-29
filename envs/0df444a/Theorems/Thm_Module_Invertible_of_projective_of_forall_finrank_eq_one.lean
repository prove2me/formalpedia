-- Prove2me | Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
-- name    : Module.Invertible.of_projective_of_forall_finrank_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/791eebfd-ee1b-5e1e-8dac-d5dc6ecaed21
-- title:
--   Finitely generated projectives of rank one at all fields are invertible
-- statement:
--   Let $A$ be a commutative ring, living in universe $u$, and let $P$ be an $A$-module (of arbitrary universe $v$) which is finitely generated and projective. Assume that for every type $K$ in the same universe $u$ as $A$, equipped with a field structure and with an $A$-algebra structure, the $K$-vector space $K \otimes_A P$ has $\operatorname{finrank}_K(K \otimes_A P) = 1$; that is, the rank condition is imposed at every field-valued point of $A$ whose underlying type lies in universe $u$ (this includes the residue fields $A/\mathfrak m$ and the residue fields of the local rings $A_{\mathfrak m}$). The conclusion is `Module.Invertible A P`: the contraction (evaluation) map $$\operatorname{contractLeft}_A P : \operatorname{Hom}_A(P,A) \otimes_A P \longrightarrow A, \qquad \varphi \otimes p \longmapsto \varphi(p),$$ is injective and surjective, so $P$ represents a class in $\operatorname{Pic}(A)$. Note that no hypothesis of finite presentation, flatness or local freeness beyond finite generation and projectivity is required, and the rank hypothesis is a statement about all field-valued base changes rather than about a rank function on $\operatorname{Spec} A$.
--
--   This is the implication "finitely generated projective of constant rank one $\Rightarrow$ invertible" in the standard equivalence between invertible modules, rank-one projective modules and line bundles on $\operatorname{Spec} A$. It is used in the scheme-theoretic part of the development, where invertible sheaves are recognised from their sections over affine charts, for instance in the treatment of relative Picard groups and of descent of invertible modules along directed systems and along faithfully flat affine morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P := by sorry
