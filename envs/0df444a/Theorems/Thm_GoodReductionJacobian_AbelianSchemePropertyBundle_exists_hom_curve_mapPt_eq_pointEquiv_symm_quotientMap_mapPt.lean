-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/86df3ddb-3ae2-59de-8c38-caa97d81aefd
-- title:
--   Lattice-linear maps of uniformisations are algebraic on curves
-- statement:
--   Let $f : G \to \operatorname{Spec}\mathbb{C}$ and $f' : G' \to \operatorname{Spec}\mathbb{C}$ be morphisms of schemes carrying relative group laws $L$, $L'$ (functorial group structures on the sets of $T$-points over $\mathbb{C}$, natural in $T$) and satisfying `AbelianSchemePropertyBundle`, i.e. each of $f$, $f'$ is smooth and proper with connected fibres and admits a relative group law. Assume every fibre of $f$ (resp. $f'$) over a point of $\operatorname{Spec}\mathbb{C}$ has topological Krull dimension $g$ (resp. $g'$). Let $\Lambda \subseteq \mathbb{C}^g$ and $\Lambda' \subseteq \mathbb{C}^{g'}$ be $\mathbb{Z}$-submodules, each spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis indexed by $\mathrm{Fin}(2g)$, resp. $\mathrm{Fin}(2g')$, and let $e$, $e'$ be bijections from the $\mathbb{C}$-points of $G$, $G'$ (morphisms $\operatorname{Spec}\mathbb{C} \to G$ over the identity) onto $\mathbb{C}^g/\Lambda$, $\mathbb{C}^{g'}/\Lambda'$, additive for the respective group laws, and such that: for each open $U$ and each $\varphi \in \Gamma(G,U)$ the locus of $v$ whose point $e^{-1}([v])$ factors through $U$ is open and $v \mapsto \varphi(e^{-1}([v]))$ is given there by a function differentiable on that locus; and around each $v_0$ there are $U$, sections $t_1,\dots,t_g$ over $U$, a radius $\varepsilon>0$ and a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^g$ such that the $\varepsilon$-ball lies in the locus for $U$, the tuple of values of the $t_i$ is there given by a map $F$, and $F$ has Fréchet derivative $D$ at $v_0$ (the same two conditions for $G'$, $e'$, $\Lambda'$). Let $T : \mathbb{C}^g \to \mathbb{C}^{g'}$ be $\mathbb{C}$-linear with $T(\Lambda) \subseteq \Lambda'$. Finally let $c : C \to \operatorname{Spec}\mathbb{C}$ be proper and smooth of relative dimension $1$ with $C$ integral, and $\nu : C \to G$ a morphism with $\nu$ followed by $f$ equal to $c$. Then there is a morphism $w : C \to G'$ with $w$ followed by $f'$ equal to $c$ such that for every $\mathbb{C}$-point $y$ of $C$ one has $w \circ y = e'^{-1}\big(\bar T (e(\nu \circ y))\big)$, where $\bar T : \mathbb{C}^g/\Lambda \to \mathbb{C}^{g'}/\Lambda'$ is the map induced by $T$.
--
--   This is the analysis-to-algebra step for complex uniformisations: a holomorphic map from a smooth proper integral curve into a complex torus uniformising an abelian scheme over $\mathbb{C}$ is induced by a morphism of schemes, the $\mathbb{C}$-points being prescribed by the lattice-linear map $\bar T$. It feeds [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap), where a morphism $G \to G'$ realising $\bar T$ is assembled from its restrictions to curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_curve_mapPt_eq_pointEquiv_symm_quotientMap_mapPt
    {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)}
    (L : RelativeGroupLaw ℂ f) (L' : RelativeGroupLaw ℂ f')
    (hA : AbelianSchemePropertyBundle ℂ f) (hA' : AbelianSchemePropertyBundle ℂ f') {g g' : ℕ}
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (hdim' : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f'.base ⁻¹' {s}) = g')
    (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hL1' : ∃ b₀ : Module.Basis (Fin (2 * g')) ℝ (Fin g' → ℂ), Λ' = Submodule.span ℤ (Set.range b₀))
    (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (he' : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f', e' (L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e' P + e' Q)
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ)))
    (hAN' : ∀ (U : G'.Opens) (φ : Γ(G', U)),
      IsOpen {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g' → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) φ)))
    (hCOV : ∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀)
    (hCOV' : ∀ v₀ : Fin g' → ℂ,
      ∃ (U : G'.Opens) (t : Fin g' → Γ(G', U)) (ε : ℝ) (D : (Fin g' → ℂ) ≃L[ℂ] (Fin g' → ℂ))
        (F : (Fin g' → ℂ) → (Fin g' → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g' => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) v₀)
    (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hT : Λ.toAddSubgroup ≤ Λ'.toAddSubgroup.comap T.toAddMonoidHom)

    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℂ)) (ν : C ⟶ G) (hν : ν ≫ f = c)
    (hC : IsProper c ∧ SmoothOfRelativeDimension 1 c ∧ IsIntegral C) :
    ∃ (w : C ⟶ G') (hw : w ≫ f' = c),
      ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) c,
        (fun P => e'.symm ((QuotientAddGroup.map Λ.toAddSubgroup Λ'.toAddSubgroup T.toAddMonoidHom hT) (e P))) (mapPt ν hν y) = mapPt w hw y := by sorry
