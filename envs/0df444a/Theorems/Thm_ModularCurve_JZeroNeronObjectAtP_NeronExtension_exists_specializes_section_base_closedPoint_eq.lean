-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_specializes_section_base_closedPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/dc83e3e0-73f3-5044-8af9-fa9fa1e7740d
-- title:
--   Points over the closed point specialise to section images
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $p$ prime and $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (the predicate `A.LiesOverPrime p`). Let $\Lambda$ be a `LevelData` for $N_0$, $p$, $A$ — a scheme over `base p` $= \operatorname{Spec}$ of the base ring, with a relative group law and parametrisations of $J_0(N_0)$-points at the generic and special points — satisfying `IsJacobian`, and let $O$ be a `JZeroNeronObjectAtP`, a commutative relative group scheme over `base p` with $J_0(N_0p)$-points, Galois and Hecke equivariance, smoothness, separatedness, local finiteness of type, quasi-compactness, surjectivity, preconnected fibres, flat surjective multiplication-by-$n$ maps, proper generic fibre, and the further data recorded in that structure. Let $F$ be an `O.NeronExtension`: a scheme `F.Nfull` with a morphism `F.gN` to `shBase A` $= \operatorname{Spec}$ of `shRing A`, the contraction of $A$ to the inertia-invariant subfield `invField A`, carrying a commutative relative group law, satisfying the Néron model property bundle over `shRing A` with fraction field `invField A` (smooth, separated, locally of finite type, quasi-compact, with the Néron unique extension property), together with an open immersion from the base change of `O.g`, a surjective specialisation homomorphism to the component group, and the compatibilities listed there. Let $n$ be a point of `F.Nfull` whose image under `F.gN` is the closed point of $\operatorname{Spec}$ `shRing A`. Then there are a point $n_0$ of `F.Nfull` and a section $\sigma$ of `F.gN` over the identity of `shBase A` (a morphism $\sigma$ from `shBase A` to `F.Nfull` with $\sigma$ followed by `F.gN` the identity) such that $n$ specialises to $n_0$ and $\sigma$ sends the closed point of $\operatorname{Spec}$ `shRing A` to $n_0$.
--
--   This is the geometric input that every point of the special fibre of the Néron extension lies in the closure of the closed-point image of an integral section, the special fibre being of finite type over an algebraically closed residue field and the base being henselian. It is used in covering `F.Nfull` by translates coming from sections, in [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_specializes_section_base_closedPoint_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_specializes_section_base_closedPoint_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) (n : ↥F.Nfull)
    (hn : F.gN.base n = IsLocalRing.closedPoint ↥(shRing A)) :
    ∃ (n₀ : ↥F.Nfull) (σ : SchemeHomOver (𝟙 (shBase A)) F.gN),
      n ⤳ n₀ ∧ σ.1.base (IsLocalRing.closedPoint ↥(shRing A)) = n₀ := by sorry
