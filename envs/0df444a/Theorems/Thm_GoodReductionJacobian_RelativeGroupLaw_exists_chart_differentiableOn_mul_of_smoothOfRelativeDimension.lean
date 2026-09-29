-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/69ee3be6-d37b-5ff4-bb16-f25114e5cea4
-- title:
--   Holomorphic chart at the identity of a smooth ℂ-group scheme
-- statement:
--   Let $G$ be a scheme and $f : G \to \operatorname{Spec}\mathbb{C}$ a morphism, and let $L$ be a relative group law for $f$ over $\mathbb{C}$: for every $\mathbb{C}$-scheme $t : T \to \operatorname{Spec}\mathbb{C}$ a multiplication, unit and inversion on the set $\{\varphi : T \to G \mid \varphi$ followed by $f$ equals $t\}$, satisfying associativity, both unit laws and left inversion, with multiplication compatible with pullback along any $\psi : T' \to T$ over $\operatorname{Spec}\mathbb{C}$. Assume $f$ satisfies `SmoothOfRelativeDimension g` for some $g \in \mathbb{N}$. Then there exist $r > 0$, a map $\psi$ from $\mathbb{C}^{g} = (\mathrm{Fin}\ g \to \mathbb{C})$ to the $\mathbb{C}$-points of $f$ (morphisms $\operatorname{Spec}\mathbb{C} \to G$ composing with $f$ to the identity), an affine open $U \subseteq G$ and sections $t_i \in \Gamma(G,U)$, $i \in \mathrm{Fin}\ g$, such that every $\psi(v)$ with $v$ in the ball $B(0,r) \subseteq \mathbb{C}^{g}$ factors through $U$ (the preimage of $U$ under $\psi(v)$ is all of $\operatorname{Spec}\mathbb{C}$), and: $\psi(0)$ is the unit point $L.\mathrm{one}$ at $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$; $\psi$ is injective on $B(0,r)$; for $v \in B(0,r)$ the value of $t_i$ at $\psi(v)$, read off via `appLE` and `Scheme.ΓSpecIso`, is $v_i$; for every open $V \subseteq G$ and every $\varphi \in \Gamma(G,V)$ the set of $v \in B(0,r)$ whose point $\psi(v)$ factors through $V$ is open and there is $F : \mathbb{C}^{g} \to \mathbb{C}$, complex differentiable on that set, with $F(v)$ equal to the value of $\varphi$ at $\psi(v)$ there; there are a finite set $\mathrm{fs} \subseteq \Gamma(G,U)$ and $\varepsilon > 0$ (the unit point itself factoring through $U$) such that every $\mathbb{C}$-point $P$ factoring through $U$ with $|\varphi(P) - \varphi(1)| < \varepsilon$ for all $\varphi \in \mathrm{fs}$ equals $\psi(v)$ for some $v \in B(0,r)$; and there are $0 < r_1 \le r$ and $M : \mathbb{C}^{g} \to \mathbb{C}^{g} \to \mathbb{C}^{g}$ with $(v,w) \mapsto M(v,w)$ complex differentiable on $B(0,r_1) \times B(0,r_1)$ and, for $v, w \in B(0,r_1)$, $M(v,w) \in B(0,r)$ and $\psi(M(v,w)) = L.\mathrm{mul}(\psi(v),\psi(w))$.
--
--   This is the algebraic-geometry-to-analysis bridge for a smooth group scheme over $\mathbb{C}$: a holomorphic coordinate chart at the identity, in which all regular functions become holomorphic and the group law is given by a holomorphic map $M$ of the coordinates. It is used in the construction of the local exponential for such a group law, [`GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_localExp_differentiableOn_appLE_of_smoothOfRelativeDimension), where the analytic part is supplied separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} (L : RelativeGroupLaw ℂ f)
    {g : ℕ} (hsm : SmoothOfRelativeDimension g f) :
    ∃ (r : ℝ) (_ : 0 < r) (ψ : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
      (U : G.Opens) (_ : IsAffineOpen U) (t : Fin g → Γ(G, U))
      (hU : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) r, ⊤ ≤ (ψ v).1 ⁻¹ᵁ U),

      ψ 0 = L.one (𝟙 (Spec (CommRingCat.of ℂ))) ∧

      Set.InjOn ψ (Metric.ball (0 : Fin g → ℂ) r) ∧

      (∀ (v : Fin g → ℂ) (hv : v ∈ Metric.ball (0 : Fin g → ℂ) r) (i : Fin g),
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE U ⊤ (hU v hv)) (t i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
        ∃ F : (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin g → ℂ | v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ ⊤ ≤ (ψ v).1 ⁻¹ᵁ V} ∧
          ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (ψ v).1 ⁻¹ᵁ V), v ∈ Metric.ball (0 : Fin g → ℂ) r →
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ v).1.appLE V ⊤ h) φ)) ∧

      (∃ (fs : Finset (Γ(G, U))) (ε : ℝ) (h1 : ⊤ ≤ (L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1 ⁻¹ᵁ U), 0 < ε ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
            (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                  (((L.one (𝟙 (Spec (CommRingCat.of ℂ)))).1.appLE U ⊤ h1) φ)‖ < ε) →
            ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, ψ v = P) ∧

      (∃ (r₁ : ℝ) (M : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ)), 0 < r₁ ∧ r₁ ≤ r ∧
          DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => M p.1 p.2)
            (Metric.ball (0 : Fin g → ℂ) r₁ ×ˢ Metric.ball (0 : Fin g → ℂ) r₁) ∧
          ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r₁ → w ∈ Metric.ball (0 : Fin g → ℂ) r₁ →
            M v w ∈ Metric.ball (0 : Fin g → ℂ) r ∧
            ψ (M v w) = L.mul (𝟙 (Spec (CommRingCat.of ℂ))) (ψ v) (ψ w)) := by sorry
