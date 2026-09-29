-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d80f6502-14ab-563e-abd2-7f8d46107775
-- title:
--   Relative analytic chart at the unit, with holomorphic multiplication
-- statement:
--   Let $S_c$ be a domain that is a finite-type smooth $\mathbb{C}$-algebra whose module of Kähler differentials over $\mathbb{C}$ has rank $1$, let $t \in S_c$, let $\sigma_0 : S_c \to \mathbb{C}$ be a $\mathbb{C}$-algebra map, let $r > 0$, and let $\mathcal{U}$ be a set of $\mathbb{C}$-algebra maps $S_c \to \mathbb{C}$ containing $\sigma_0$ such that $\sigma \mapsto \sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t), r)$ and every $s \in S_c$ is given on $\mathcal{U}$ by a function holomorphic on that ball, i.e. $\sigma(s) = F_s(\sigma(t))$. Let $f : G \to \operatorname{Spec} S_c$ be smooth of relative dimension $g$, carrying a relative group law $L$: functorial operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\{\varphi : T \to G \mid \varphi \text{ followed by } f = t\}$ for test schemes $t : T \to \operatorname{Spec} S_c$, satisfying the group axioms and naturality in $T$. Let $\sigma_1 \in \mathcal{U}$ be such that $(\ker \sigma_1) \cdot \Omega + S_c \cdot dt = \Omega$. Then there exist $\varepsilon, \rho' > 0$ with $B(\sigma_1(t), \varepsilon) \subseteq B(\sigma_0(t), r)$, an affine open $U_1 \subseteq G$, coordinates $s_1 : \mathrm{Fin}\,g \to \Gamma(G, U_1)$, a centre $v_1 \in \mathbb{C}^g$ and a family $\psi_1$ assigning to each $\sigma$ and each $v \in \mathbb{C}^g$ a $\mathbb{C}$-point of $G$ over $\operatorname{Spec}(\sigma)$, such that all $\psi_1(\sigma, v)$ with $\sigma \in \mathcal{U}$, $\sigma(t) \in B(\sigma_1(t), \varepsilon)$ and $v \in B(v_1, \rho')$ factor through $U_1$, as does the unit at $\sigma_1$, and: (i) $\psi_1(\sigma_1, v_1)$ is the unit at $\sigma_1$; (ii) $s_1(i)$ evaluated at $\psi_1(\sigma, v)$ is $v_i$; (iii) for every open $V$ and $\varphi \in \Gamma(G, V)$ the set of pairs $(z, v)$ in $B(\sigma_1(t), \varepsilon) \times B(v_1, \rho')$ for which some $\sigma \in \mathcal{U}$ has $\sigma(t) = z$ and $\psi_1(\sigma, v)$ factoring through $V$ is open, and there is a function holomorphic on it whose value at $(\sigma(t), v)$ is $\varphi$ evaluated at $\psi_1(\sigma, v)$; (iv) there are a finite set of sections in $\Gamma(G, U_1)$ and $\eta_1 > 0$ such that any $\sigma$-point $P$ factoring through $U_1$ whose values on those sections are within $\eta_1$ of those of the unit at $\sigma_1$ equals $\psi_1(\sigma, v)$ for some $v \in B(v_1, \rho')$; (v) there is a map $o$, holomorphic on $B(\sigma_1(t), \varepsilon)$, with $o(\sigma(t)) \in B(v_1, \rho')$ and $\psi_1(\sigma, o(\sigma(t)))$ the unit at $\sigma$; and (vi) there are $0 < \rho_2 \le \rho'$ and $M$, holomorphic on $B(\sigma_1(t), \varepsilon) \times B(v_1, \rho_2) \times B(v_1, \rho_2)$ jointly in all variables, with $M(\sigma(t), v, w) \in B(v_1, \rho')$ and $\psi_1(\sigma, M(\sigma(t), v, w)) = L.\mathrm{mul}$ at $\sigma$ of $\psi_1(\sigma, v)$ and $\psi_1(\sigma, w)$.
--
--   This is the relative version, over a one-dimensional analytic chart of the base, of the construction of a local analytic chart at the identity of a group scheme in which the multiplication becomes a holomorphic map of the coordinates; the chart varies holomorphically with the base parameter $\sigma(t)$, and the unit section is holomorphic in it. It is the input to the holomorphic uniformisation of families of fake elliptic curves, being cited in the construction of a local holomorphic uniformising family near the origin for the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relChart_one_differentiableOn_mul_of_analyticChart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relChart_one_differentiableOn_mul_of_analyticChart

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f) {g : ℕ} (hsm : SmoothOfRelativeDimension g f)
    (σ₁ : Sc →ₐ[ℂ] ℂ) (hσ₁ : σ₁ ∈ 𝒰)
    (hdt₁ : ((RingHom.ker σ₁.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
        Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤)) :
    ∃ (ε ρ' : ℝ) (_ : 0 < ε) (_ : 0 < ρ') (_ : Metric.ball (σ₁ t) ε ⊆ Metric.ball (σ₀ t) r)
      (U₁ : G.Opens) (_ : IsAffineOpen U₁) (s₁ : Fin g → Γ(G, U₁)) (v₁ : Fin g → ℂ)
      (ψ₁ : (σ : Sc →ₐ[ℂ] ℂ) → (Fin g → ℂ) → SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f)
      (hU₁ : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ U₁)
      (h1U₁ : ⊤ ≤ (L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1 ⁻¹ᵁ U₁),

      ψ₁ σ₁ v₁ = L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom)) ∧

      (∀ (σ : Sc →ₐ[ℂ] ℂ) (hσ : σ ∈ 𝒰) (hz : σ t ∈ Metric.ball (σ₁ t) ε) (v : Fin g → ℂ) (hv : v ∈ Metric.ball v₁ ρ')
        (i : Fin g), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE U₁ ⊤ (hU₁ σ hσ hz v hv)) (s₁ i)) = v i) ∧

      (∀ (V : G.Opens) (φ : Γ(G, V)),
        IsOpen {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin g → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin g → ℂ) | p.1 ∈ Metric.ball (σ₁ t) ε ∧ p.2 ∈ Metric.ball v₁ ρ' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (ψ₁ σ p.2).1 ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ', ∀ (hV : ⊤ ≤ (ψ₁ σ v).1 ⁻¹ᵁ V),
            F (σ t, v) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((ψ₁ σ v).1.appLE V ⊤ hV) φ)) ∧

      (∃ (fs₁ : Finset (Γ(G, U₁))) (η₁ : ℝ), 0 < η₁ ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          ∀ (P : SchemeHomOver (Spec.map (CommRingCat.ofHom σ.toRingHom)) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U₁),
            (∀ φ ∈ fs₁, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P).1.appLE U₁ ⊤ hP) φ) - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((L.one (Spec.map (CommRingCat.ofHom σ₁.toRingHom))).1.appLE U₁ ⊤ h1U₁) φ)‖ < η₁) →
            ∃ v ∈ Metric.ball v₁ ρ', ψ₁ σ v = P) ∧

      (∃ o : ℂ → (Fin g → ℂ), DifferentiableOn ℂ o (Metric.ball (σ₁ t) ε) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε →
          o (σ t) ∈ Metric.ball v₁ ρ' ∧ ψ₁ σ (o (σ t)) = L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))) ∧

      (∃ (ρ₂ : ℝ) (M : ℂ → (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ)), 0 < ρ₂ ∧ ρ₂ ≤ ρ' ∧
        DifferentiableOn ℂ (fun p : ℂ × ((Fin g → ℂ) × (Fin g → ℂ)) => M p.1 p.2.1 p.2.2)
          (Metric.ball (σ₁ t) ε ×ˢ (Metric.ball v₁ ρ₂ ×ˢ Metric.ball v₁ ρ₂)) ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε → ∀ v ∈ Metric.ball v₁ ρ₂, ∀ w ∈ Metric.ball v₁ ρ₂,
          M (σ t) v w ∈ Metric.ball v₁ ρ' ∧
          ψ₁ σ (M (σ t) v w) = L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) (ψ₁ σ v) (ψ₁ σ w)) := by sorry
