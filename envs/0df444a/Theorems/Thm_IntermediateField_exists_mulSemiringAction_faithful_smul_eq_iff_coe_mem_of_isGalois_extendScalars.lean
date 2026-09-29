-- Prove2me | Theorems.Thm_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
-- name    : IntermediateField.exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/de2df3d5-5d28-5aec-b392-4d2a93da7908
-- title:
--   Gal(E/F) as a faithful finite action on E with fixed field F
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $F$ and $E$ be intermediate fields of $L/K$ with $F \le E$. Write $E'$ for `IntermediateField.extendScalars hle`, that is, $E$ viewed as an intermediate field of the extension $L/F$, and assume that $E'$ is finite-dimensional over $F$ and that $E'/F$ is Galois. The conclusion asserts the existence of a type $G$ (in the same universe as $L$) together with a group structure on $G$, a `Fintype` structure on $G$, and an action of $G$ on the subfield $E$ by ring automorphisms (a `MulSemiringAction G ↥E`), such that: the action is faithful, i.e. two elements of $G$ acting identically on $E$ are equal; every $g \in G$ fixes each $x \in E$ whose image in $L$ lies in $F$; and conversely, any $x \in E$ with $g \cdot x = x$ for all $g \in G$ has image in $L$ lying in $F$. Thus the invariants of the action are exactly the elements of $E$ coming from $F$.
--
--   This is Artin's description of a finite Galois extension: the Galois group $\mathrm{Gal}(E/F)$ acts faithfully on $E$ with fixed field exactly $F$, packaged so that the acting group and the action are produced existentially on the type $\uparrow E$ itself rather than on the $F$-algebra `IntermediateField.extendScalars hle`. It is used in this form by the statements about chart rings of the modular curve $X_1$, namely [`ModularCurve.XOneP.exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_algEquiv_chartAlgFin_comap_eq_of_comap_eq_twoChartIntegralModel_x1_mul) and [`ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul`](thm.html#ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IntermediateField.exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (F E : IntermediateField K L) (hle : F ≤ E)
    [FiniteDimensional ↥F ↥(IntermediateField.extendScalars hle)]
    [IsGalois ↥F ↥(IntermediateField.extendScalars hle)] :
    ∃ (G : Type v) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥E),
      FaithfulSMul G ↥E ∧
      (∀ (g : G) (x : ↥E), (x : L) ∈ F → g • x = x) ∧
      (∀ x : ↥E, (∀ g : G, g • x = x) → (x : L) ∈ F) := by sorry
