-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/cda19d34-b273-5a35-8a12-c9c657d3e147
-- title:
--   Globalising a fibrewise additive holomorphic family of points
-- statement:
--   Let $Sc$ be a domain which is a finitely generated smooth $\mathbb{C}$-algebra with $\operatorname{rank}_{Sc}\Omega_{Sc/\mathbb{C}}=1$, let $t\in Sc$, let $\sigma_0:Sc\to\mathbb{C}$ be a $\mathbb{C}$-algebra map, $r>0$, and let $\mathcal{U}$ be a set of $\mathbb{C}$-points of $Sc$ containing $\sigma_0$ on which $\sigma\mapsto\sigma t$ is a bijection onto the ball $B(\sigma_0 t,r)$, each $s\in Sc$ being given on $\mathcal{U}$ by a function of $\sigma t$ holomorphic on that ball. Let $f:G\to\operatorname{Spec} Sc$ be separated and smooth of relative dimension $2$, equipped with a `RelativeGroupLaw` $L$: a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverses, and naturality under base change) on the sets $\{\varphi:T\to G\mid \varphi\,;f=t\}$ for all $t:T\to\operatorname{Spec} Sc$. Let $Pf$ assign to each character $\sigma$ and each $w\in\mathbb{C}^2$ a $\mathbb{C}$-point of $G$, and let $\varepsilon_0,r'>0$ with $\varepsilon_0\le r$. The hypotheses on $Pf$ are: each $Pf\,\sigma\,w$ lies over $\sigma$ for $\sigma\in\mathcal{U}$; $w\mapsto Pf\,\sigma\,w$ is additive for the group law in the fibre over $\sigma$; for every open $V\subseteq G$ and $\varphi\in\Gamma(G,V)$ the locus of $(p_1,p_2)$ with $p_1\in B(\sigma_0 t,\varepsilon_0)$, $p_2\in B(0,r')$ and $Pf\,\sigma\,p_2$ factoring through $V$ for some $\sigma\in\mathcal{U}$ with $\sigma t=p_1$ is open, and the pullback of $\varphi$ along $Pf\,\sigma\,w$ is the restriction to it of a function holomorphic there; and for each $\sigma_1\in\mathcal{U}$ with $\sigma_1 t\in B(\sigma_0t,\varepsilon_0)$ and each $w_1\in\mathbb{C}^2$ there are $V$, sections $f_2,f_3\in\Gamma(G,V)$, $\delta>0$ and a map $F$ on $\mathbb{C}^2$ given on $B(w_1,\delta)$ by the values of $(f_2,f_3)$ at $Pf\,\sigma_1\,w$, with Fréchet derivative at $w_1$ a continuous linear automorphism of $\mathbb{C}^2$. Then there is $\varepsilon$ with $0<\varepsilon\le\varepsilon_0$ such that four assertions hold. (i) For every $V$ and every $f\in\Gamma(G,V)$, the locus of $(p_1,p_2)$ with $p_1\in B(\sigma_0t,\varepsilon)$ and $Pf\,\sigma\,p_2$ factoring through $V$ for some $\sigma\in\mathcal{U}$ with $\sigma t=p_1$ is open — with no restriction on $p_2$ — and the pullback of $f$ along $Pf\,\sigma\,w$ is the restriction of a function holomorphic there. (ii) For $\sigma_1\in\mathcal{U}$ with $\sigma_1t\in B(\sigma_0t,\varepsilon)$ and any $w_1,w_1'$ with $Pf\,\sigma_1\,w_1=Pf\,\sigma_1\,w_1'$, there are $V$ through which $Pf\,\sigma_1\,w_1$ factors, sections $f_2,f_3\in\Gamma(G,V)$, $\delta>0$, continuous linear automorphisms $D,D'$ of $\mathbb{C}\times\mathbb{C}^2$ and $\Phi$ on $\mathbb{C}\times\mathbb{C}^2$ such that the $\delta$-balls about $(\sigma_1t,w_1)$ and $(\sigma_1t,w_1')$ lie in the locus of (i) for $V$, on those balls $\Phi(\sigma t,w)=(\sigma t,(f_2,f_3)(Pf\,\sigma\,w))$, $\Phi$ has derivative $D$ at $(\sigma_1t,w_1)$ and $D'$ at $(\sigma_1t,w_1')$, and whenever $(\sigma t,w)$ and $(\sigma t,w')$ lie in the first and the second ball respectively and the values of $f_2$ and of $f_3$ agree at $Pf\,\sigma\,w$ and $Pf\,\sigma\,w'$, then $Pf\,\sigma\,w=Pf\,\sigma\,w'$. (iii) For each $w$ with $Pf\,\sigma_0\,w$ not the unit section over $\sigma_0$ there is $\delta$ with $0<\delta\le\varepsilon$ such that for all $\sigma\in\mathcal{U}$ with $\sigma t\in B(\sigma_0t,\delta)$ and all $w'$ with $Pf\,\sigma\,w'$ the unit section over $\sigma$ one has $\|w'-w\|\ge\delta$. (iv) For $\sigma_1\in\mathcal{U}$ with $\sigma_1t\in B(\sigma_0t,\varepsilon)$, any $w_1$ and any $\rho>0$, there are $V$ through which $Pf\,\sigma_1\,w_1$ factors, a finite set $fs$ of sections of $\Gamma(G,V)$ and $\varepsilon_1>0$ such that every $\mathbb{C}$-point $P$ of $G$ over a character $\sigma\in\mathcal{U}$ with $\sigma t\in B(\sigma_1t,\varepsilon_1)$ which factors through $V$ and whose values on all members of $fs$ are within $\varepsilon_1$ of those of $Pf\,\sigma_1\,w_1$ is of the form $Pf\,\sigma\,w$ for some $w\in B(w_1,\rho)$.
--
--   This is the globalisation step for a holomorphically varying family of relative exponential maps: the local analyticity and chart hypotheses, assumed only for parameters $w$ near $0$, are propagated to all $w$ by repeated division by $n$ in the relative group law, yielding joint holomorphy, local invertibility with a common algebraic chart at coincident points, discreteness of the period locus and local surjectivity onto nearby points. It feeds the construction of holomorphic uniformisations of fake elliptic curves in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f)
    (hsep : IsSeparated f) (hsm : SmoothOfRelativeDimension 2 f)

    (Pf : (Sc →ₐ[ℂ] ℂ) → (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
    (ε₀ r' : ℝ) (hε₀ : 0 < ε₀) (hε₀r : ε₀ ≤ r) (hr' : 0 < r')

    (hOVER : ∀ σ ∈ 𝒰, ∀ w : Fin 2 → ℂ, (Pf σ w) ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))

    (hHOM : ∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ)
      (hw : (Pf σ w) ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
      (hw' : (Pf σ w') ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom)),
      (L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟨(Pf σ w), hw⟩ ⟨(Pf σ w'), hw'⟩).1 = (Pf σ (w + w')))

    (hLOCAN : ∀ (V : G.Opens) (φ : Γ(G, V)),
      IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₀ ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
      ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₀ ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε₀ → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
          F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ w)).appLE V ⊤ hV) φ))

    (hFIBCOV : ∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε₀ → ∀ w₁ : Fin 2 → ℂ,
      ∃ (V : G.Opens) (f₂ f₃ : Γ(G, V)) (δ : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
        (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
        0 < δ ∧
        (∀ w ∈ Metric.ball w₁ δ, ⊤ ≤ (Pf σ₁ w) ⁻¹ᵁ V) ∧
        (∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (Pf σ₁ w) ⁻¹ᵁ V), w ∈ Metric.ball w₁ δ →
          F w = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ₁ w)).appLE V ⊤ hV) f₂),
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ₁ w)).appLE V ⊤ hV) f₃)]) ∧
        HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧

      (∀ (V : G.Opens) (f : Γ(G, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((Pf σ w).appLE V ⊤ hV) f)) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (Pf σ₁ w₁) =
          (Pf σ₁ w₁') →
        ∃ (V : G.Opens) (f₂ f₃ : Γ(G, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (Pf σ₁ w₁) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (Pf σ w') ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w').appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w').appLE V ⊤ hV') f₃) →
              (Pf σ w) =
                (Pf σ w'))) ∧

      (∀ w : Fin 2 → ℂ, Pf σ₀ w ≠ (L.one (Spec.map (CommRingCat.ofHom σ₀.toRingHom))).1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) δ → ∀ w' : Fin 2 → ℂ,
          Pf σ w' = (L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 → δ ≤ ‖w' - w‖) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : G.Opens) (fs : Finset ↑(Γ(G, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (Pf σ₁ w₁) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : Spec (CommRingCat.of ℂ) ⟶ G) (hPσ : P ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
              (hP : ⊤ ≤ P ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ₁ w₁).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ, P = Pf σ w) := by sorry
