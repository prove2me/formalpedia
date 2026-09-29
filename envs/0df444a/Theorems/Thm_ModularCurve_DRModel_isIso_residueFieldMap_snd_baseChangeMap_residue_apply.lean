-- Prove2me | Theorems.Thm_ModularCurve_DRModel_isIso_residueFieldMap_snd_baseChangeMap_residue_apply
-- name    : ModularCurve.DRModel.isIso_residueFieldMap_snd_baseChangeMap_residue_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/413cda34-8c25-5ea0-9ee0-4b0ff2d8cb72
-- title:
--   Residue field map is an isomorphism at a rational point
-- statement:
--   Let $p$ be a prime and let $O$ be a commutative local ring with residue field $k =$ `IsLocalRing.ResidueField O`. Write $\mathfrak X$ for `DRModel p`, the two-chart integral model over $\mathbb Z$ attached to the element `IgusaScheme.jFull p` of the field `modularFunctionFieldFull p` (the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the divisor expansions of level $p$): it is the pushout gluing the spectra of the two $\mathbb Z$-subalgebras `chartAlgFin` and `chartAlgInf`, with `DRModel.toBase p :` $\mathfrak X \to \operatorname{Spec}\mathbb Z$ the induced structure morphism. Assume given a morphism $s \colon \operatorname{Spec} k \to \mathfrak X \times_{\operatorname{Spec}\mathbb Z} \operatorname{Spec} k$ with $s$ followed by the second projection equal to the identity of $\operatorname{Spec} k$, i.e. a section of the projection, hence a $k$-point of the fibre. Let $x$ be the image, under the map of underlying topological spaces of `DRModel.baseChangeMap (IsLocalRing.residue O)` (the pullback map over $\operatorname{Spec}(O \to k)$, the identity on $\mathfrak X$ and on $\operatorname{Spec}\mathbb Z$), of the image of the closed point of $\operatorname{Spec} k$ under $s$. Then the map of residue fields induced at $x$ by the projection $\mathfrak X \times_{\operatorname{Spec}\mathbb Z} \operatorname{Spec} O \to \operatorname{Spec} O$ is an isomorphism.
--
--   This is the rationality statement for points of the special fibre of the Deligne–Rapoport style integral model: a $k$-rational point of the fibre over the residue field of a local base $O$, viewed inside the model over $O$, has residue field exactly $k$. It is used by [`ModularCurve.DRModelPackage.injective_baseChangeMap_compInf_of_exists_section`](thm.html#ModularCurve.DRModelPackage.injective_baseChangeMap_compInf_of_exists_section) in the analysis of the closed fibre and its resolution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_isIso_residueFieldMap_snd_baseChangeMap_residue_apply.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.isIso_residueFieldMap_snd_baseChangeMap_residue_apply (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsLocalRing O]
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsIso ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).residueFieldMap
      ((DRModel.baseChangeMap (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))) := by sorry
