-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/9d1a024d-c198-5fd0-8ab8-49f3785327ca
-- title:
--   Linear maps of complex uniformisations come from scheme homomorphisms
-- statement:
--   Let $f : G \to \operatorname{Spec}\mathbb{C}$ and $f' : G' \to \operatorname{Spec}\mathbb{C}$ be morphisms of schemes (universe $0$) equipped with relative group laws $L$, $L'$ — functorial multiplication, unit and inverse on $T$-points $\{\varphi : T \to G \mid \varphi \circ f = t\}$ satisfying the group axioms and compatible with base change — and suppose each satisfies `AbelianSchemePropertyBundle`, i.e. is smooth, proper, has connected fibres and admits some relative group law. Assume every fibre of $f$ has topological Krull dimension $g$ and every fibre of $f'$ has dimension $g'$. Let $\Lambda \le \mathbb{C}^g$ and $\Lambda' \le \mathbb{C}^{g'}$ be $\mathbb{Z}$-submodules, each spanned over $\mathbb{Z}$ by the range of some $\mathbb{R}$-basis of the ambient space (indexed by $\mathrm{Fin}(2g)$, resp. $\mathrm{Fin}(2g')$), and let $e$, $e'$ be bijections from the $\mathbb{C}$-points (sections over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$) of $f$, $f'$ onto $\mathbb{C}^g/\Lambda$, $\mathbb{C}^{g'}/\Lambda'$ carrying the group law to addition. Two analyticity packages are assumed for each side: for every open $U$ and every $\varphi \in \Gamma(G,U)$ the set of $v$ whose point $e^{-1}(v)$ factors through $U$ is open and $v \mapsto \varphi(e^{-1}(v))$ agrees there with a function holomorphic on that set; and near every $v_0$ there are $U$, a $g$-tuple of sections over $U$ and $\varepsilon > 0$ such that all $v$ in the ball of radius $\varepsilon$ factor through $U$ and the resulting $\mathbb{C}^g$-valued function has at $v_0$ a derivative which is a linear homeomorphism. Finally let $T : \mathbb{C}^g \to \mathbb{C}^{g'}$ be $\mathbb{C}$-linear with $\Lambda \subseteq T^{-1}(\Lambda')$. Then there exist $u : G \to G'$ with $u$ followed by $f'$ equal to $f$ such that, for every scheme $S$ and every $s : S \to \operatorname{Spec}\mathbb{C}$, composition with $u$ is multiplicative on $S$-points, and on $\mathbb{C}$-points it is $e'^{-1} \circ \bar T \circ e$, where $\bar T$ is the induced map $\mathbb{C}^g/\Lambda \to \mathbb{C}^{g'}/\Lambda'$.
--
--   This is the algebraicity statement that a $\mathbb{C}$-linear map of the uniformising spaces carrying one lattice into the other is induced by a homomorphism of the abelian schemes over $\mathbb{C}$, in the form needed for quaternionic moduli: it is used in [`CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic`](thm.html#CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic) to recognise endomorphisms of a uniformised abelian surface.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology
open AlgebraicGeometry

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_pointEquiv_symm_quotientMap_of_le_comap
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
    (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hT : Λ.toAddSubgroup ≤ Λ'.toAddSubgroup.comap T.toAddMonoidHom) :
    ∃ (u : G ⟶ G') (hu : u ≫ f' = f),

      (∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver s f),
        mapPt u hu (L.mul s P Q) = L'.mul s (mapPt u hu P) (mapPt u hu Q)) ∧

      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
        mapPt u hu P = (fun P => e'.symm ((QuotientAddGroup.map Λ.toAddSubgroup Λ'.toAddSubgroup T.toAddMonoidHom hT) (e P))) P) := by sorry
