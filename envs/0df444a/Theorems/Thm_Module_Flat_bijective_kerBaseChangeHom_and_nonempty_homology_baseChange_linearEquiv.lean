-- Prove2me | Theorems.Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
-- name    : Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/a74b5b0b-0332-5e17-91c8-622b0206b038
-- title:
--   Flat base change commutes with kernels and homology
-- statement:
--   Let $R$ be a commutative ring and $T$ a commutative $R$-algebra that is flat as an $R$-module, and let $f : M \to N$ and $g : N \to P$ be $R$-linear maps between $R$-modules $M$, $N$, $P$ (all in one universe) with $g \circ f = 0$. Write $g \otimes T$ for the base-changed map $T \otimes_R N \to T \otimes_R P$, and let [`TwoChartCech.kerBaseChangeHom`](def/AlgebraicGeometry_TwoChartCech.html#L123) applied to $g$ and $T$ be the canonical $T$-linear map $T \otimes_R \ker g \to \ker(g \otimes T)$ obtained by base changing the inclusion $\ker g \hookrightarrow N$ and corestricting it to $\ker(g \otimes T)$ (legitimate since $g \circ (\ker g \hookrightarrow N) = 0$). The assertion is fourfold: (i) this map is bijective; (ii) there exists a $T$-linear isomorphism $T \otimes_R \bigl(\ker g / (\operatorname{range} f \cap \ker g)\bigr) \cong \ker(g \otimes T) / (\operatorname{range}(f \otimes T) \cap \ker(g \otimes T))$, where in each case the intersection is the preimage of the range under the inclusion of the kernel; (iii) $\ker(g \otimes T) \le \operatorname{range}(f \otimes T)$ holds if and only if $T \otimes_R \bigl(\ker g / (\operatorname{range} f \cap \ker g)\bigr)$ is subsingleton; and (iv) if the homology $\ker g / (\operatorname{range} f \cap \ker g)$ is a finite $R$-module, then $\ker(g \otimes T) / (\operatorname{range}(f \otimes T) \cap \ker(g \otimes T))$ is a finite $T$-module.
--
--   This is the standard statement that a flat base change $R \to T$ — for instance a localisation $R \to R_{\mathfrak p}$ or $R \to R_g$, or a field extension — commutes with kernels and with the homology of a two-term complex of modules, in the $\ker/\operatorname{range}$ spelling used for the rows of a two-chart Čech complex. It is used in the Zariski-local analysis of when the base-changed complex becomes exact, notably by [`Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range`](thm.html#Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
    {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T]
    {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g ∘ₗ f = 0) :
    letI : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
      Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
    Function.Bijective (TwoChartCech.kerBaseChangeHom g T) ∧
    Nonempty
      (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
        (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) ∧
    ((LinearMap.ker (g.baseChange T) ≤ LinearMap.range (f.baseChange T)) ↔
        Subsingleton (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype))) ∧
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) →
        Module.Finite T (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) := by sorry
