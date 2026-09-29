-- Prove2me | Theorems.Thm_GroupCohomology_RepCokernel_seq_shortExact
-- name    : GroupCohomology.RepCokernel.seq_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f815ff98-507e-5e3f-8146-745e019176eb
-- title:
--   Cokernel sequence of an injective morphism of representations is short exact
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $f \colon X \to Y$ be a morphism in the category $\mathrm{Rep}_k(G)$ of $k$-linear representations of $G$. Assume that the underlying $k$-linear map `f.hom` is injective as a function. Then the short complex [`GroupCohomology.RepCokernel.seq f`](def/GroupCohomology_RepCokernel.html#L27) is short exact. That complex has $X_1 = X$, $X_2 = Y$ and $X_3 =$ [`GroupCohomology.RepCokernel.obj f`](def/GroupCohomology_RepCokernel.html#L13), the explicit cokernel construction whose underlying $k$-module is the quotient of $Y$ by the image of $f$ (with the induced $G$-action), its first map is $f$ itself and its second map is the projection [`GroupCohomology.RepCokernel.π f`](def/GroupCohomology_RepCokernel.html#L18) onto that quotient; the composite is zero because every class $\mathrm{mk}(f(x))$ vanishes. Short exactness asserts the three conditions: $f$ is a monomorphism in $\mathrm{Rep}_k(G)$, `π f` is an epimorphism, and the complex is exact at $Y$. Thus $0 \to X \xrightarrow{f} Y \to Y/f(X) \to 0$ is a short exact sequence of representations.
--
--   This is the basic short exact sequence attached to an injective morphism of $G$-representations, the input for dimension-shifting and long exact sequence arguments in group cohomology. It is used in the treatment of cohomology of idèle groups, for instance in [`NumberField.IdeleLocalInv.map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation`](thm.html#NumberField.IdeleLocalInv.map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation) and [`NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside`](thm.html#NumberField.SIdele.injective_map_H2_of_injective_of_range_eq_unitIdelesOutside).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepCokernel_seq_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepCokernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory

theorem GroupCohomology.RepCokernel.seq_shortExact {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) : (GroupCohomology.RepCokernel.seq f).ShortExact := by sorry
