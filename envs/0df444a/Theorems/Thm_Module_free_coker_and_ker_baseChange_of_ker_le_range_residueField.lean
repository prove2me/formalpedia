-- Prove2me | Theorems.Thm_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField
-- name    : Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/f2dc5093-ef76-5b11-af50-9c507d2cb41f
-- title:
--   Base change in degree 0 for a complex with finite free tail
-- statement:
--   Let $R$ be a commutative local ring with residue field $\kappa =$ `IsLocalRing.ResidueField R`, and let $C_0, C_1, C_2$ be $R$-modules with $C_1$ and $C_2$ finite and free over $R$ ($C_0$ is arbitrary). Let $d_0 : C_0 \to C_1$ and $d_1 : C_1 \to C_2$ be $R$-linear maps with $d_1 \circ d_0 = 0$, and assume that after base change to the residue field the complex is exact in the middle in the one direction that does not come for free, namely $\ker(d_1 \otimes \kappa) \le \operatorname{im}(d_0 \otimes \kappa)$ as submodules of $\kappa \otimes_R C_1$. The conclusion is the conjunction of two assertions: first, the cokernel $C_1 / \operatorname{im} d_0$ is a free $R$-module; second, for every commutative $R$-algebra $A$ (taken in the same universe as $R$), the base change along $A$ of the inclusion $\ker d_0 \hookrightarrow C_0$, as a map $A \otimes_R \ker d_0 \to A \otimes_R C_0$, has image exactly $\ker(d_0 \otimes A)$ and is injective. Thus $A \otimes_R \ker d_0 \to \ker(d_0 \otimes_R A)$ is an isomorphism for all such $A$.
--
--   This is the elementary local case of "cohomology and base change" in degree $0$: vanishing of $H^1$ of the complex after reduction to the residue field forces $H^0 = \ker d_0$ to commute with arbitrary base change, and the cokernel of $d_0$ to be free. It is used to obtain the corresponding statement over a field in [`Module.ker_baseChange_field_of_subsingleton_H1_of_projective`](thm.html#Module.ker_baseChange_field_of_subsingleton_H1_of_projective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_coker_and_ker_baseChange_of_ker_le_range_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open TensorProduct

theorem Module.free_coker_and_ker_baseChange_of_ker_le_range_residueField
    (R : Type u) [CommRing R] [IsLocalRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2] [Module.Finite R C1] [Module.Free R C1] [Module.Finite R C2] [Module.Free R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (hH1 : LinearMap.ker (d1.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range (d0.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (C1 ⧸ LinearMap.range d0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        LinearMap.range ((LinearMap.ker d0).subtype.baseChange A) = LinearMap.ker (d0.baseChange A) ∧
          Function.Injective ((LinearMap.ker d0).subtype.baseChange A) := by sorry
