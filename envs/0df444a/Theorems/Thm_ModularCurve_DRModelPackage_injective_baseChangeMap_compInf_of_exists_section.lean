-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_injective_baseChangeMap_compInf_of_exists_section
-- name    : ModularCurve.DRModelPackage.injective_baseChangeMap_compInf_of_exists_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/95453c6f-2a87-5d6c-82ed-444a9f23f191
-- title:
--   Injectivity of the node map into the model over O
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a `DRModelPackage p`, i.e. a package of data and properties for the two-chart integral model `DRModel p` of the full modular function field with the Igusa $j$-invariant over $\mathbb Z$, whose structure morphism is `DRModel.toBase p`; among its fields are two morphisms `𝔛.compInf κ` and `𝔛.compZero κ` into the base change of `DRModel p` along $\mathbb Z \to \kappa$. Let $O$ be a commutative local ring, $\kappa$ an algebraically closed field of characteristic $p$, and $toκ : O \to \kappa$ a ring homomorphism. Write $X_O$ and $X_\kappa$ for the pullbacks of `DRModel.toBase p` along $\operatorname{Spec}$ of $\mathbb Z \to O$ and $\mathbb Z \to \kappa$, and $X_{k}$ for the corresponding pullback over the residue field $k$ of $O$; `DRModel.baseChangeMap` gives the induced morphisms $X_\kappa \to X_O$ and $X_{k} \to X_O$. Assume, for every point $x$ of the fibre product of `𝔛.compInf κ` and `𝔛.compZero κ`, that there is a morphism $s : \operatorname{Spec} k \to X_{k}$ splitting the projection to $\operatorname{Spec} k$ (its composite with the second projection is the identity) and such that the image of $x$ in $X_O$, formed by the first projection followed by `𝔛.compInf κ` and then `DRModel.baseChangeMap toκ` on underlying spaces, equals the image under `DRModel.baseChangeMap (IsLocalRing.residue O)` of $s$ applied to the closed point of $\operatorname{Spec} k$. Then the resulting map from points of that fibre product to points of $X_O$ is injective.
--
--   The fibre product of the two component morphisms plays the role of the set of crossing points of the $p$-fibre of the Deligne–Rapoport model, and the statement says that distinct crossing points have distinct images in the model over $O$ once each of them comes from a $k$-rational point of the fibre over the residue field. It is used in the construction of the resolved model together with its charts, in [`ModularCurve.DRModelPackage.exists_dRResolvedModelPackageV4_and_dRResolvedModelCharts`](thm.html#ModularCurve.DRModelPackage.exists_dRResolvedModelPackageV4_and_dRResolvedModelCharts), where it yields pairwise distinct, hence separable, chart neighbourhoods of the nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_injective_baseChangeMap_compInf_of_exists_section.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.injective_baseChangeMap_compInf_of_exists_section (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsLocalRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base x) =
          (DRModel.baseChangeMap (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))) :
    Function.Injective fun n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) =>
      (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base n) := by sorry
