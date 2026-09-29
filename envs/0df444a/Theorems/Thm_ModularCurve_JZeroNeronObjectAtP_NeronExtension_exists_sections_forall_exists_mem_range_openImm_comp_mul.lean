-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d3cbf110-8d35-5e53-9e9e-f396617915bd
-- title:
--   Néron model as union of component-group translates
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $p$ prime and $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbf Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$. Let $\Lambda$ be a level datum of level $(N_0,p)$ for $A$ satisfying `Λ.IsJacobian`, let $O$ be a Néron object at $p$ for these data, and let $F$ be a Néron extension of $O$, with structure morphism `F.gN` from `F.Nfull` to $\operatorname{Spec}$ of the ring `shRing A`, relative group law `F.LN`, open immersion `F.openImm` from the base change of $O$'s group scheme, and component map `F.specN` to `componentGroup O.width` (the quotient of the dual of the character lattice by the image of the Gram map of the widths). The assertion is that there is a family $y$, indexed by `componentGroup O.width`, of sections of `F.gN` over the base (morphisms $y_\varphi$ from the base to `F.Nfull` with $y_\varphi$ followed by `F.gN` the identity) such that: first, for each $\varphi$, `F.specN` of the point obtained by composing `shPt A` with $y_\varphi$ equals $\varphi$; second, every point $n$ of the underlying space of `F.Nfull` lies in the image, on points, of `F.openImm` followed by translation by $y_\varphi$ for some $\varphi$, translation being `F.LN.mul` applied to the identity of `F.Nfull` and to `F.gN` followed by $y_\varphi$.
--
--   This is the classical description of the Néron model over a strictly henselian discrete valuation ring as the union of the translates of its identity component by a set of representatives of the component group, phrased for the Néron extension datum of $J_0(N_0p)$ at a place above $p$. It is used in establishing flatness, quasi-compactness and local quasi-finiteness of multiplication by $n$ on the Néron extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∃ y : componentGroup O.width → SchemeHomOver (𝟙 (shBase A)) F.gN,

      (∀ φ, F.specN ⟨shPt A ≫ (y φ).1,
          (Category.assoc _ _ _).trans ((congrArg (shPt A ≫ ·) (y φ).2).trans (Category.comp_id _))⟩ = φ) ∧

      (∀ n : ↥F.Nfull, ∃ φ,
        n ∈ Set.range (F.openImm.1 ≫
          (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩
            ⟨F.gN ≫ (y φ).1,
              (Category.assoc _ _ _).trans ((congrArg (F.gN ≫ ·) (y φ).2).trans (Category.comp_id F.gN))⟩).1).base) := by sorry
