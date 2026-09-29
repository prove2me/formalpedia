-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_differentiableOn_appLE_one_of_analyticChart
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_differentiableOn_appLE_one_of_analyticChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b56ac80d-bc55-5aa3-9146-b91fd56f6138
-- title:
--   Holomorphy of sections at the unit point over an analytic chart
-- statement:
--   Let $S_c$ be a commutative domain that is a ℂ-algebra of finite type, smooth over $\mathbb{C}$, whose module of Kähler differentials $\Omega_{S_c/\mathbb{C}}$ has rank $1$ over $S_c$; let $t \in S_c$, let $\sigma_0 : S_c \to \mathbb{C}$ be a $\mathbb{C}$-algebra homomorphism, let $r > 0$ and let $\mathcal{U}$ be a set of $\mathbb{C}$-algebra homomorphisms $S_c \to \mathbb{C}$ with $\sigma_0 \in \mathcal{U}$, such that $\sigma \mapsto \sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t), r)$ and such that for every $s \in S_c$ there is a function $F$ complex-differentiable on $B(\sigma_0(t), r)$ with $\sigma(s) = F(\sigma(t))$ for all $\sigma \in \mathcal{U}$. Let $f : G \to \operatorname{Spec} S_c$ be a morphism of schemes and let $L$ be a relative group law on $f$, that is, a group structure on the set of lifts $\{\varphi : T \to G \mid \varphi \circ f = t\}$ for every scheme $T$ and every $t : T \to \operatorname{Spec} S_c$, with multiplication natural in $T$. Fix $\sigma_1 \in \mathcal{U}$, an open $V \subseteq G$ whose preimage under the unit lift $1_{\sigma_1} := L.\mathrm{one}(\operatorname{Spec} \sigma_1) : \operatorname{Spec} \mathbb{C} \to G$ is all of $\operatorname{Spec} \mathbb{C}$, and a section $\varphi \in \Gamma(G, V)$. Then there are $\varepsilon > 0$ and $F : \mathbb{C} \to \mathbb{C}$ with $B(\sigma_1(t), \varepsilon) \subseteq B(\sigma_0(t), r)$, $F$ complex-differentiable on $B(\sigma_1(t), \varepsilon)$, and such that for every $\sigma \in \mathcal{U}$ with $\sigma(t) \in B(\sigma_1(t), \varepsilon)$ the unit lift $1_\sigma$ likewise factors through $V$ and $F(\sigma(t))$ equals the complex number obtained from $\varphi$ by pulling it back along $1_\sigma$ and identifying $\Gamma(\operatorname{Spec} \mathbb{C}, \top)$ with $\mathbb{C}$.
--
--   This is the statement that, over an affine analytic chart of a smooth curve over $\mathbb{C}$, the value of any regular function near the unit point of a relative group law varies holomorphically with the chart parameter. It is used in the analytic study of the group law on such schemes, in particular by [`GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_differentiableOn_appLE_one_of_analyticChart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_differentiableOn_appLE_one_of_analyticChart
    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (V : G.Opens) (h1V : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 ⁻¹ᵁ V) (φ : Γ(G, V)) :
    ∃ (ε : ℝ) (F : ℂ → ℂ), 0 < ε ∧ Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r ∧
      DifferentiableOn ℂ F (Metric.ball (σ₁ t) ε) ∧
      ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
        ∃ h : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 ⁻¹ᵁ V,
          F (σ t) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
            (((L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1.appLE V ⊤ h) φ) := by sorry
