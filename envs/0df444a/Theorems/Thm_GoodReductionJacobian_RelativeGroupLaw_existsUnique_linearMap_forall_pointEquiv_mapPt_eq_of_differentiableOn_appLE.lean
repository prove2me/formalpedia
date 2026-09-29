-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/ce12e0d2-df30-57d3-a98b-44c41a8512bb
-- title:
--   Homomorphisms of complex-uniformised group schemes lift to linear maps
-- statement:
--   Let $f : G \to \operatorname{Spec}\mathbb{C}$ and $f' : G' \to \operatorname{Spec}\mathbb{C}$ be schemes over $\mathbb{C}$ equipped with relative group laws $L$, $L'$: functorial multiplication, unit and inversion on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$, satisfying the group axioms and compatible with change of the test object $T$. Let $g,g' \in \mathbb{N}$, let $\Lambda \subseteq \mathbb{C}^g$ and $\Lambda' \subseteq \mathbb{C}^{g'}$ be $\mathbb{Z}$-submodules, and let $e$, $e'$ be bijections from the $\mathbb{C}$-points (sections over the identity of $\operatorname{Spec}\mathbb{C}$) of $f$, resp. $f'$, onto $\mathbb{C}^g/\Lambda$, resp. $\mathbb{C}^{g'}/\Lambda'$. Assume: $\Lambda'$ is the $\mathbb{Z}$-span of the range of an $\mathbb{R}$-basis of $\mathbb{C}^{g'}$ indexed by $\mathrm{Fin}(2g')$; $e$ and $e'$ carry the group laws to addition; (analyticity, for $G$ and for $G'$) for every open $U$ and section $\varphi \in \Gamma(U)$ the set of $v$ whose point $e^{-1}[v]$ factors through $U$ is open and $v \mapsto \varphi(e^{-1}[v])$ agrees there with a function differentiable on that set; (local chart at every $v_0 \in \mathbb{C}^{g'}$) there are an open $U$, sections $t_1,\dots,t_{g'}$ on $U$, $\varepsilon>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^{g'}$ and $F$ agreeing on the ball $B(v_0,\varepsilon)$ — all of whose points factor through $U$ — with $v \mapsto (t_i(e'^{-1}[v]))_i$, such that $F$ has Fréchet derivative $D$ at $v_0$; (local surjectivity) for all $v_0$ and $r>0$ there are an open $U$ containing the image of $e'^{-1}[v_0]$, a finite set $S$ of sections on $U$ and $\varepsilon>0$ such that any $\mathbb{C}$-point $P$ factoring through $U$ with $|\varphi(P)-\varphi(e'^{-1}[v_0])|<\varepsilon$ for all $\varphi \in S$ satisfies $e'P = [w]$ for some $w \in B(v_0,r)$. Finally let $u : G \to G'$ satisfy $u$ followed by $f'$ equals $f$, and assume that composition with $u$ is a homomorphism on $\mathbb{C}$-points. Then there is a unique $\mathbb{C}$-linear map $T : \mathbb{C}^g \to \mathbb{C}^{g'}$ with $T(\Lambda) \subseteq \Lambda'$ such that $e'(P \circ u) = [Tv]$ whenever $eP = [v]$.
--
--   This is the algebraic-geometry form of the classical fact that a homomorphism of complex tori lifts uniquely to a $\mathbb{C}$-linear map of the universal covers carrying one lattice into the other, with the analytic input on the two group schemes supplied as explicit hypotheses about values of sections at uniformised points. It is used in the Čerednik–Drinfel'd quaternionic moduli development, in the characterisation [`CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic`](thm.html#CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic) of when a morphism of uniformised group schemes comes from a map of lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
    {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)}
    (L : RelativeGroupLaw ℂ f) (L' : RelativeGroupLaw ℂ f') {g g' : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

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

    (hCOV' : ∀ v₀ : Fin g' → ℂ,
      ∃ (U : G'.Opens) (t : Fin g' → Γ(G', U)) (ε : ℝ) (D : (Fin g' → ℂ) ≃L[ℂ] (Fin g' → ℂ))
        (F : (Fin g' → ℂ) → (Fin g' → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g' => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) v₀)

    (hSURJ' : ∀ (v₀ : Fin g' → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G'.Opens) (fs : Finset (Γ(G', U))) (ε : ℝ) (h₀ : ⊤ ≤ (e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f') (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e' P = (w : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

    (u : G ⟶ G') (hu : u ≫ f' = f)
    (hhom : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q)) :
    ∃! T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
      (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (v : Fin g → ℂ),
        e P = (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) →
        e' (mapPt u hu P) = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) := by sorry
