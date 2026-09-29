-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/6423aed9-20ad-55cb-a171-871f97ee10cb
-- title:
--   Complex uniformisation: G(ℂ)≅ℂ^g/Λ with holomorphic charts
-- statement:
--   Let $G$ be a scheme and $f : G \to \operatorname{Spec}\mathbb{C}$ a morphism, equipped with a relative group law $L$ over $\mathbb{C}$, that is, functorial group operations `mul`, `one`, `inv` on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to G$ over a given $t : T \to \operatorname{Spec}\mathbb{C}$, satisfying associativity, the unit and inverse laws and compatibility with base change, and assumed commutative ($hc$). Assume further the bundle `AbelianSchemePropertyBundle`: $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists; and assume that for every point $s$ of $\operatorname{Spec}\mathbb{C}$ the fibre $f^{-1}(s)$ has topological Krull dimension $g$. Then there are a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{C}^g$ (written $\mathbb{C}^g = (\mathrm{Fin}\,g \to \mathbb{C})$) and a bijection $e$ from the sections of $f$ over the identity of $\operatorname{Spec}\mathbb{C}$ onto $\mathbb{C}^g/\Lambda$ such that: (i) $\Lambda$ is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^g$ indexed by $\mathrm{Fin}(2g)$, so a lattice; (ii) $e(L.\mathrm{mul}\,P\,Q) = e(P)+e(Q)$; (iii) for every open $U \subseteq G$ and every $\varphi \in \Gamma(G,U)$, the set of $v \in \mathbb{C}^g$ for which the point $e^{-1}([v])$ factors through $U$ is open, and there is $F : \mathbb{C}^g \to \mathbb{C}$, differentiable on that set, whose value at such $v$ is the scalar obtained from $\varphi$ by restriction along $e^{-1}([v])$ (via `appLE` and `Scheme.ΓSpecIso`); (iv) for every $v_0 \in \mathbb{C}^g$ there are an open $U$, sections $t_1,\dots,t_g \in \Gamma(G,U)$, a radius $\varepsilon > 0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^g$ and $F : \mathbb{C}^g \to \mathbb{C}^g$ such that every $v$ in the ball $B(v_0,\varepsilon)$ has $e^{-1}([v])$ factoring through $U$, $F(v) = (t_i(e^{-1}([v])))_{i}$ on that ball, and $F$ has Fréchet derivative $D$ at $v_0$.
--
--   This is the complex uniformisation theorem for abelian varieties, in the functor-of-points formulation used throughout: the $\mathbb{C}$-points of an abelian scheme over $\mathbb{C}$ of fibre dimension $g$ form a complex torus $\mathbb{C}^g/\Lambda$, with global sections pulling back to holomorphic functions of the uniformising variable and with $g$ sections giving a local chart at each point. It is invoked in the Čerednik–Drinfeld part of the development, by [`CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic`](thm.html#CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_submodule_pointEquiv_quotient_differentiableOn_appLE.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle ℂ f) {g : ℕ}
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ℂ)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ))
      (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)),

      (∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀)) ∧

      (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q) ∧

      (∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) ∧

      (∀ v₀ : Fin g → ℂ,
      ∃ (U : G.Opens) (t : Fin g → Γ(G, U)) (ε : ℝ) (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
        (F : (Fin g → ℂ) → (Fin g → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀) := by sorry
