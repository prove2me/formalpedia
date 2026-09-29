-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/2dceda05-95b1-5c31-9e20-802bf774657f
-- title:
--   Local exponential of a smooth commutative group scheme over ℂ
-- statement:
--   Let $G$ be a scheme, $f : G \to \operatorname{Spec}\mathbb{C}$ a morphism, and $L$ a relative group law on $f$ over $\mathbb{C}$, i.e. a rule assigning to every $t : T \to \operatorname{Spec}\mathbb{C}$ a multiplication, unit and inversion on the set of morphisms $T \to G$ over $t$, satisfying associativity, the two unit laws, left inversion, and naturality of multiplication under base change along $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$; assume $L$ is commutative (multiplication is commutative for every $t$), and that $f$ is smooth of relative dimension $g$. Then there are $r > 0$, a map $\exp_0$ from $\mathbb{C}^g = (\mathrm{Fin}\,g \to \mathbb{C})$ to the set of morphisms $\operatorname{Spec}\mathbb{C} \to G$ over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$, an affine open $U \subseteq G$ and sections $t_i \in \Gamma(G,U)$ ($i \in \mathrm{Fin}\,g$) such that every $\exp_0 v$ with $v$ in the ball $B(0,r)$ has preimage of $U$ all of $\operatorname{Spec}\mathbb{C}$ (witnessed by $hU$), and: $\exp_0 0$ is the unit point $L.\mathrm{one}$; $\exp_0(v+w) = L.\mathrm{mul}(\exp_0 v, \exp_0 w)$ whenever $v, w, v+w \in B(0,r)$; $\exp_0$ is injective on $B(0,r)$; for every open $V \subseteq G$ and every $\varphi \in \Gamma(G,V)$ the set $S_V$ of $v \in B(0,r)$ whose point factors through $V$ (preimage of $V$ equal to $\top$) is open, and some $F : \mathbb{C}^g \to \mathbb{C}$ is differentiable on $S_V$ and satisfies, for $v \in B(0,r)$ factoring through $V$, $F v =$ the scalar obtained from $\varphi$ by the restriction map $(\exp_0 v)^{\sharp}$ along $V \supseteq \top$ read through `Scheme.ΓSpecIso`; there are a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^g$ and a map $F : \mathbb{C}^g \to \mathbb{C}^g$ agreeing on $B(0,r)$ with $v \mapsto (t_i(\exp_0 v))_i$ in the same sense and having Fréchet derivative $D$ at $0$; and finally there are a finite set $fs \subseteq \Gamma(G,U)$, a bound $\varepsilon > 0$ and a proof that the unit point lies in $U$, such that every point $P : \operatorname{Spec}\mathbb{C} \to G$ over the identity lying in $U$ with $|\varphi(P) - \varphi(1)| < \varepsilon$ for all $\varphi \in fs$ equals $\exp_0 v$ for some $v \in B(0,r)$.
--
--   This is the germ at the identity of the classical exponential map $\operatorname{Lie} G \to G(\mathbb{C})$ for a smooth commutative group scheme over $\mathbb{C}$, formulated purely scheme-theoretically: charts are recorded as values of sections at $\mathbb{C}$-points, the group law is transported through the functorial multiplication of $L$, and local surjectivity onto a neighbourhood of the identity is expressed by finitely many test sections. It rests on the existence of an analytic chart at the identity together with the construction of a local exponential for a holomorphic commutative local group law, and is used in building the complex uniformisation of an abelian scheme, namely in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_submodule_pointEquiv_quotient_differentiableOn_appLE).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f) (hc : L.IsCommutative)
    {g : ℕ} (hsm : SmoothOfRelativeDimension g f) :
    ∃ (r : ℝ) (_ : 0 < r) (exp₀ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
      (U : G.Opens) (_ : IsAffineOpen U) (t : Fin g → Γ(G, U))
      (hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ U),

      exp₀ 0 = L.one (𝟙 (Spec (CommRingCat.of ℂ))) ∧

      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r → w ∈ Metric.ball (0 : Fin g → ℂ) r →
        v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
        exp₀ (v + w) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (exp₀ v) (exp₀ w)) ∧

      Set.InjOn exp₀ (Metric.ball (0 : Fin g → ℂ) r) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
        ∃ F : (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V} ∧
          ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (exp₀ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE V ⊤ h) φ)) ∧

      (∃ (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (F : (Fin g → ℂ) → (Fin g → ℂ)),
          (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r),
            F v = fun i : Fin g =>
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((exp₀ v).1.appLE U ⊤ (hU v hv)) (t i))) ∧
          HasFDerivAt F (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0) ∧

      (∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
            ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, exp₀ v = P) := by sorry
