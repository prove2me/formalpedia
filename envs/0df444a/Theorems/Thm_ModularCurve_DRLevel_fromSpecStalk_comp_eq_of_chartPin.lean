-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin
-- name    : ModularCurve.DRLevel.fromSpecStalk_comp_eq_of_chartPin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/6cfcfca2-0528-58be-9e4a-7a4e0c024e26
-- title:
--   Chart-pinned models of the special fibre agree generically
-- statement:
--   Fix $N_0, q \in \mathbb{N}$ with $N_0 \neq 0$, $q$ prime and $q \nmid N_0$, an algebraically closed field $\kappa$ of characteristic $q$ with decidable equality, and a ring homomorphism $\mathrm{to}\kappa \colon \mathrm{R}\,q \to \kappa$. Let $\mathrm{fibre0}$ be the pullback of $\mathrm{toBase0}\,N_0\,q = \mathrm{igusaTo}\,N_0\,q \colon \mathrm{X0}\,N_0\,q \to \operatorname{Spec}(\mathrm{R}\,q)$ along $\operatorname{Spec}(\mathrm{to}\kappa)$. Let $M$ and $M'$ be two data of type `CurveModel` over $\kappa$ for the field $L =$ `modularFunctionFieldC` $\kappa\,N_0$, the subfield of $\kappa((q))$ generated over $\kappa$ by $\mathrm{jqModC}\,\kappa$ and $\mathrm{jqNModC}\,\kappa\,N_0$; thus each consists of an integral scheme with a proper smooth relative-dimension-one morphism to $\operatorname{Spec}\kappa$, a ring isomorphism `ffEquiv` of $L$ with its function field compatible with $\kappa$, and a bijection of its closed points with the places of $L/\kappa$ matching stalks with valuation rings. Suppose given isomorphisms $e \colon M.C \to \mathrm{fibre0}$ and $e' \colon M'.C \to \mathrm{fibre0}$ which are morphisms over $\operatorname{Spec}\kappa$, i.e. $e$ followed by the second projection is $M.\mathrm{toBase}$ and likewise for $e'$, such that the preimage under $e$, resp. $e'$, followed by the first projection, of the open image of the finite chart $\iota_{\mathrm{Fin}}\,N_0\,q$ is nonempty. Assume both models are pinned on that chart: for every element $b$ of the $\mathbb{Z}_{(q)}$-subalgebra `chartAlgFin` $N_0\,q$ of `modularFunctionFieldFull` $N_0 \subset \mathbb{Q}((q))$, reading $b$ as a global section of the chart, pulling it back along $e$ followed by the first projection, taking its germ at the generic point and transporting it through $M.\mathrm{ffEquiv}^{-1}$ to an element $\mathrm{read}_b \in L$, one has $\mathrm{read}_b = \mathrm{jGeomGen}\,\kappa\,N_0$ whenever $b = \mathrm{jChartFin}\,N_0\,q$, and $\mathrm{read}_b = \mathrm{jNGeomGen}\,\kappa\,N_0$ whenever the $q$-expansion of $b$ in $\mathbb{Q}((q))$ equals $\mathrm{qExpand}\,\mathbb{Q}\,N_0\,\mathrm{jq}$; and the same two conditions for $M'$, $e'$. The conclusion is that $M.C.\mathrm{fromSpecStalk}$ at the generic point of $M.C$, followed by $e$ and then by $e'^{-1}$, equals $\operatorname{Spec}$ of the ring homomorphism $M.\mathrm{ffEquiv} \circ (M'.\mathrm{ffEquiv})^{-1} \colon M'.C.\mathrm{functionField} \to M.C.\mathrm{functionField}$ followed by $M'.C.\mathrm{fromSpecStalk}$ at the generic point of $M'.C$.
--
--   This is the uniqueness half of the dictionary between the special fibre of the Igusa/Deligne–Rapoport model of $X_0(N_0)$ in characteristic $q$ and abstract smooth proper models of the characteristic-$q$ modular function field: any two models pinned by the values of the two chart generators $j$ and $j(q^{N_0})$ are compared by an isomorphism which, on generic points, is induced by the identity of the function field under the two identifications. It feeds the identification of the point–place correspondence with the arithmetic Frobenius action in [`ModularCurve.DRLevel.pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul`](thm.html#ModularCurve.DRLevel.pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_fromSpecStalk_comp_eq_of_chartPin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRLevel.fromSpecStalk_comp_eq_of_chartPin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))

    (M' : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e' : M'.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e']
    (heM' : e' ≫ pullback.snd _ _ = M'.toBase)
    [hMne' : Nonempty (Scheme.Opens.toScheme ((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin' : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb' : ↥(modularFunctionFieldC κ N₀) :=
          M'.ffEquiv.symm
            (M'.C.germToFunctionField
              ((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e' ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb' = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb' = jNGeomGen κ N₀))) :
    M.C.fromSpecStalk (genericPoint M.C) ≫ e ≫ inv e' =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp M'.ffEquiv.symm.toRingHom)) ≫
        M'.C.fromSpecStalk (genericPoint M'.C) := by sorry
