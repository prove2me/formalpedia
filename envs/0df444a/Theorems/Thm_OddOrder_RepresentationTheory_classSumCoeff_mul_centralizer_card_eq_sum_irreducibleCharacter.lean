-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
-- name    : OddOrder.RepresentationTheory.classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:08.608754+00:00
-- url     : https://prove2.me/theorems/41c8e22b-9a3a-43fa-864b-9dbdde862f30
-- title:
--   Class-sum coefficient times a centralizer order as a sum over irreducible characters
-- statement:
--   Let $G$ be a finite group and let $C_i,C_j,C_s$ be conjugacy classes of $G$. Let $a_{ijs}$ be the class-sum coefficient, the number of pairs $(u,v)\in G\times G$ with $u\in C_i$, $v\in C_j$, $uv\in C_s$ (`classSumCoeff`). Let $s$ be a chosen representative of $C_s$ (`Cs.out`), and similarly $x_i,x_j$ for $C_i,C_j$. Then in $\mathbb{C}$,
--   $$a_{ijs}\cdot|C_G(s)|=\sum_{\chi\in\mathrm{Irr}(G)}\frac{|C_i|\,\chi(x_i)\cdot|C_j|\,\chi(x_j)}{\chi(1)}\;\chi(s^{-1}).$$
--
--   This is the class-sum coefficient formula with the centralizer factor left explicit: multiplying the pair-count coefficient by $|C_G(s)|$ inverts the single-character central-character product formula by column orthogonality.
--
--   **Formalization Note** The sum runs over `IrreducibleCharacter G`, viewed as class functions `G → ℂ`; $|C_i|$ is `Nat.card {x // ConjClasses.mk x = Ci}`; $|C_G(s)|$ is `Nat.card (Subgroup.centralizer {Cs.out})`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassSumCoefficientFormula.lean#L119-L210

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory.CenterClassSum

variable {G : Type*} [Group G]

section Formula

variable [Fintype G] [DecidableEq (ConjClasses G)]

theorem classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
    (Ci Cj Cs : ConjClasses G) :
    (classSumCoeff Ci Cj Cs : ℂ) *
        (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) =
      ∑ χ : IrreducibleCharacter G,
        (((Nat.card { x : G // ConjClasses.mk x = Ci } : ℂ) *
            (χ : ClassFunction G ℂ) Ci.out *
          ((Nat.card { x : G // ConjClasses.mk x = Cj } : ℂ) *
            (χ : ClassFunction G ℂ) Cj.out)) /
          (χ : ClassFunction G ℂ) (1 : G)) *
          (χ : ClassFunction G ℂ) Cs.out⁻¹ := by sorry

end Formula

end OddOrder.RepresentationTheory
