-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind
-- name    : GroupCohomology.RepPi.forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f4c63830-6740-5701-851e-f75d117f8556
-- title:
--   Assembling local conditions across a product of coinduced representations
-- statement:
--   Let $G$ be a group, $\iota$ an index set, and for each $i\in\iota$ let $D_i\le G$ be a subgroup and $Y_i$ a $\mathbb{Z}$-linear representation of $D_i$. Let $f\colon R\to P$ be a morphism of $\mathbb{Z}$-linear representations of $G$, let $T_i$ be additive commutative groups, and for each $i$ let $\Lambda_i\colon \operatorname{Hom}_{D_i}(\operatorname{Res}_{D_i}R,\,Y_i)\to T_i$ be an additive map. Assume each $\Lambda_i$ is surjective, and that for every $s\colon \operatorname{Res}_{D_i}R\to Y_i$ one has $\Lambda_i(s)=0$ exactly when $s$ factors as $\operatorname{Res}_{D_i}f$ followed by some $\chi\colon \operatorname{Res}_{D_i}P\to Y_i$. Write $J$ for the representation whose underlying module is $\prod_i \operatorname{Coind}_{D_i}^{G}Y_i$ with $G$ acting componentwise, equipped with its projections $\mathrm{pr}_i$, and for $s\colon R\to J$ let $s_i\colon \operatorname{Res}_{D_i}R\to Y_i$ be the image of $s$ followed by $\mathrm{pr}_i$ under the inverse of the hom-equivalence of the adjunction $\operatorname{Res}_{D_i}\dashv\operatorname{Coind}_{D_i}^{G}$. The conclusion is a conjunction: first, for every $t\in\prod_i T_i$ there is $s\colon R\to J$ with $\Lambda_i(s_i)=t_i$ for all $i$; second, for every $s\colon R\to J$, all $\Lambda_i(s_i)$ vanish if and only if $s=f$ followed by some $\chi\colon P\to J$.
--
--   This is the assembly step that turns per-place data — surjectivity of the local maps $\Lambda_i$ together with a description of their kernels as the morphisms factoring through $f$ — into the same two properties for the single map $s\mapsto(\Lambda_i(s_i))_i$ on morphisms into the product of the coinduced representations, the passage between global and local homs being Frobenius reciprocity. It is used in the construction of global degree-one classes with prescribed local components and in the nondegeneracy argument for the associated pairing on Selmer-type groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem GroupCohomology.RepPi.forall_exists_comp_proj_and_iff_exists_eq_comp_of_coind
    {G : Type} [Group G] {ι : Type} [Finite ι] (D : ι → Subgroup G) (Y : ∀ i, Rep ℤ ↥(D i))
    {R P : Rep ℤ G} (f : R ⟶ P)
    (T : ι → Type) [∀ i, AddCommGroup (T i)]
    (Λ : ∀ i, (Rep.res (D i).subtype R ⟶ Y i) →+ T i)
    (hsurj : ∀ i, Function.Surjective (Λ i))
    (hker : ∀ (i) (s : Rep.res (D i).subtype R ⟶ Y i),
      Λ i s = 0 ↔ ∃ χ : Rep.res (D i).subtype P ⟶ Y i, s = (Rep.resFunctor (D i).subtype).map f ≫ χ) :
    (∀ t : ∀ i, T i, ∃ s : R ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)),
        ∀ i, Λ i (((Rep.resCoindAdjunction ℤ (D i).subtype).homEquiv R (Y i)).symm
          (s ≫ GroupCohomology.RepPi.proj (fun i => Rep.coind (D i).subtype (Y i)) i)) = t i) ∧
    (∀ s : R ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)),
        (∀ i, Λ i (((Rep.resCoindAdjunction ℤ (D i).subtype).homEquiv R (Y i)).symm
          (s ≫ GroupCohomology.RepPi.proj (fun i => Rep.coind (D i).subtype (Y i)) i)) = 0) ↔
        ∃ χ : P ⟶ GroupCohomology.RepPi.obj (fun i => Rep.coind (D i).subtype (Y i)), s = f ≫ χ) := by sorry
