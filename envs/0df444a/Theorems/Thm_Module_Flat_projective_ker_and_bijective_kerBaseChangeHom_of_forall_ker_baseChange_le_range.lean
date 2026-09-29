-- Prove2me | Theorems.Thm_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
-- name    : Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/19ba377e-133a-59bf-82ac-f0084fc68a30
-- title:
--   Base change for a bounded complex of flat modules
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C_i$ ($i \in \mathbb{N}$) be $R$-modules, each flat, equipped with $R$-linear maps $d_i : C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$. Assume the complex is bounded: there is an $n$ with $C_i$ a subsingleton (i.e. zero) for all $i \ge n$. Assume further that $\ker d_0$ is a finite $R$-module, that for every $i$ the cohomology module $\ker d_{i+1} / (d_i(C_i) \cap \ker d_{i+1})$ — formally, the quotient of $\ker d_{i+1}$ by the pullback of $\operatorname{range} d_i$ along the inclusion of $\ker d_{i+1}$ — is a finite $R$-module, and that for every field $K$ carrying an $R$-algebra structure and every $i$ one has $\ker(d_{i+1} \otimes_R K) \le \operatorname{range}(d_i \otimes_R K)$, where $\otimes_R K$ denotes base change of linear maps. Then: $\ker d_0$ is a projective $R$-module; for every commutative $R$-algebra $A$ the comparison map [`TwoChartCech.kerBaseChangeHom`](def/AlgebraicGeometry_TwoChartCech.html#L123), namely the $A$-linear map $A \otimes_R \ker d_0 \to \ker(d_0 \otimes_R A)$ obtained by base changing the inclusion $\ker d_0 \hookrightarrow C_0$ and corestricting to $\ker(d_0 \otimes_R A)$, is bijective; and for every commutative $R$-algebra $A$ and every $i$, $\ker(d_{i+1} \otimes_R A) \le \operatorname{range}(d_i \otimes_R A)$. All modules, fields and algebras here live in the same universe as $R$.
--
--   This is the commutative-algebra form of cohomology and base change: vanishing of the higher cohomology of a bounded complex of flat modules with finitely generated cohomology on all field-valued fibres forces $H^0$ to be projective and to commute with arbitrary base change, the higher vanishing persisting after any base change. It is used for the Čech complex of a module on a flat family with a finite affine cover, via [`AlgebraicGeometry.Scheme.Modules.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc`](thm.html#AlgebraicGeometry.Scheme.Modules.finite_projective_sections_and_exists_linearEquiv_tensorProduct_pullbackLocalSection_of_forall_subsingleton_HSucc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) :
    Module.Projective R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by sorry
