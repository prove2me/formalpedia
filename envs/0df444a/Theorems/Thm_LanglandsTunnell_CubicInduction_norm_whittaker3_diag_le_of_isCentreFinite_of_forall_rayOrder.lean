-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
-- name    : LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/986faac2-7e58-51e8-bf3e-1f9b3c39705a
-- title:
--   Uniform two-variable torus bound for GL₃ Whittaker coefficients
-- statement:
--   Fix real numbers $\theta_0,\theta$ with $\theta<\theta_0$ and natural numbers $N,N_2,N_3$. The assertion is that there exists a natural number $N'$, depending only on these data, such that the following holds for every group homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ and every function $u$ on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ with complex values subject to: $u$ is continuous; $u(\gamma g)=u(g)$ for $\gamma$ in the image of $\mathrm{GL}_3(\mathbb{Q})$ under the adelic structure map; $u(zg)=\omega(z)u(g)$ for $z$ a central adelic scalar; [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. for each $g$ the function $e\mapsto u(g\cdot \mathrm{archRealLift3}(e))$ is $C^\infty$ on the set of real $3\times3$ matrices $e$ with $\det e\neq 0$; there is a finite set $s$ of functions such that for every $k$ whose component at each finite place is $1$ and whose archimedean component $k$ satisfies $k^{\mathsf T}k=1$, the translate $g\mapsto u(gk)$ lies in the $\mathbb{C}$-span of $s$; there are coefficients $a\colon \mathrm{Fin}(N_2+1)\to\mathbb{C}$ with $a(N_2)=1$ and $\sum_m a_m\,\mathrm{casimir2}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\partial_{ij}\partial_{ji}\varphi$ with $\partial_{ij}$ the right derivative at $0$ along $1+sE_{ij}$ at the archimedean place, and likewise coefficients monic of degree $N_3$ annihilating $u$ in $\mathrm{casimir3}\,\varphi=\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}\varphi$; for every word $w$ in pairs $(i,j)$ the iterated derivative $\partial_w u$ satisfies $\lVert \partial_w u(g)\rVert\le C\,\mathrm{gauge3}(g)^N$ for some $C$, where $\mathrm{gauge3}(g)=\max(1,\mathrm{archGauge3}(g)\cdot\mathrm{finGauge3}(g))$; and finally, for every $k$ with archimedean component satisfying $k^{\mathsf T}k=1$, the Whittaker integral $W$ of the translate $g\mapsto u(gk)$, taken with respect to the standard additive character $\psi_\mathbb{Q}$ of $\mathbb{A}_\mathbb{Q}$ and the carrier data $\mathrm{productionPinsOf}\,\mathbb{Q}\,\emptyset\,(\bot)\,(1)\,(\mathrm{adelicBox}\,\mathbb{Q})$, evaluated at the archimedean diagonal lift of $\mathrm{diag}(y_1y_2,y_2,1)$, obeys a bound $C\,y_1^{\theta_0}$ for $0<y_1\le1$ at each fixed $y_2>0$, and a bound $C\,y_2^{\theta_0}$ for $0<y_2\le1$ at each fixed $y_1>0$. Under these hypotheses, for every compact set $K\subseteq \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ there is a constant $C$ such that for all $k\in K$ and all $y_1,y_2>0$ the Whittaker integral of $u$ itself at the diagonal lift of $\mathrm{diag}(y_1y_2,y_2,1)$ times $k$ is bounded in norm by $C\,(\min(y_1,1)^{\theta}\max(y_1,1)^{N'})\,(\min(y_2,1)^{\theta}\max(y_2,1)^{N'})$.
--
--   This is the two-variable growth-and-decay estimate for the $\psi$-Whittaker coefficient of an automorphic function on $\mathrm{GL}_3$ over $\mathbb{Q}$ along the archimedean diagonal torus $\mathrm{diag}(y_1y_2,y_2,1)$: exponent $\theta$ (any value below the given ray-wise order $\theta_0$) in the small-$y$ directions and a uniform polynomial exponent $N'$ in the large-$y$ directions, with the constant uniform over compact sets of right translates. It feeds the corresponding bound for finite linear combinations of right translates within the cubic induction block used for the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.norm_whittaker3_diag_le_of_isCentreFinite_of_forall_rayOrder
    (θ₀ θ : ℝ) (hθ : θ < θ₀) (N N₂ N₃ : ℕ) :
    ∃ N' : ℕ, ∀ (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      Continuous u →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∃ a : Fin (N₂ + 1) → ℂ, a (Fin.last N₂) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∃ a : Fin (N₃ + 1) → ℂ, a (Fin.last N₃) = 1 ∧ ∑ m, a m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
        (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by sorry
