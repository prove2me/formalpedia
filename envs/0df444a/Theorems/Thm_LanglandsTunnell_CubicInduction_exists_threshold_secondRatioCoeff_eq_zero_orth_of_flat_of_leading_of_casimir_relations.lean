-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/59823c95-5096-531c-9b09-6501fbdc8fb8
-- title:
--   Flat leading Whittaker coefficients vanish at orthogonal translates
-- statement:
--   Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$, and let $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ be monic coefficient vectors, i.e. $a_2(N_2)=a_3(N_3)=1$. Then there is a threshold $\rho_0\in\mathbb{R}$, depending only on these data, with the following property. Let $\rho\ge\rho_0$, let $n,J,N\in\mathbb{N}$, let $e:\mathrm{Fin}\,n\to\mathbb{C}$ be injective with $\operatorname{Re}e_i\le\rho$ for all $i$, and let $\delta>0$. Let $u:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ satisfy: all iterated archimedean directional derivatives `WhittakerBlock.archDeriv` of $u$ along words $w$ in the elementary directions $1+sE_{ij}$ are continuous; $u$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$; $u(zg)=\omega(z)u(g)$ for central ideles $z$; [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), that is, $e\mapsto u(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det\ne 0\}$ for each $g$; a finiteness condition, namely a finite set $s$ of functions such that $g\mapsto u(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ trivial at all finite places whose archimedean component lies in `orth3`, the set of matrices with $k^{\mathsf T}k=1$; the two Casimir relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{ji}\varphi$ and $\mathrm{casimir3}\,\varphi=\sum_{i,j,k}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{jk}\mathrm{archDeriv}_{ki}\varphi$; and moderate growth $\|\partial_w u(g)\|\le C\,\mathrm{gauge3}(g)^N$ for each word $w$, where $\mathrm{gauge3}(g)=\max(1,\mathrm{archGauge3}(g)\,\mathrm{finGauge3}(g))$. Let $c_{ij}(y_1,k)$ be functions, jointly continuous on $\{y_1>0\}$, which expand the Whittaker integral `whittaker3` of $u$ against the standard additive character $\psi_\mathbb{Q}$ and the carrier pins $\mathrm{productionPinsOf}\ \mathbb{Q}\ \emptyset\ \bot\ 1$ on the adelic box, in the sense that for every compact $K$ and every $b\ge 1$ there is $C$ with $$\Big\|W_u\big(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\big)-\sum_{i,j}c_{ij}(y_1,k)\,y_2^{e_i}(\log y_2)^{j}\Big\|\le C\,y_2^{\rho+\delta}$$ for $k\in K$, $b^{-1}\le y_1\le b$ and $0<y_2\le 1$. Fix indices $i,j$ such that $c_{i''j''}(y_1,k)=0$ for all $k$, all $y_1>0$ and all $i'',j''$ with $\operatorname{Re}e_{i''}<\operatorname{Re}e_i$ (leading), and such that for every $j'\ge j$ and every compact $K$ there is $C$ with $\|c_{ij'}(y_1,k)\|\le C\,y_1^{\rho+\delta}$ for $k\in K$ and $0<y_1\le 1$ (flatness). Then for every $g_0$ whose archimedean component lies in `orth3`, every $j'\ge j$ and every $y_1>0$, one has $c_{ij'}(y_1,g_0)=0$.
--
--   This is the vanishing half of the non-triviality analysis of the two-parameter asymptotic expansion of Casimir-finite Whittaker functions on $\mathrm{GL}_3$ over $\mathbb{Q}$: a leading exponent whose coefficient functions are flat in the first ratio variable must vanish identically at archimedean-orthogonal translates. It feeds the corresponding statement for arbitrary translates, which removes the orthogonality restriction by $K$-finiteness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ → Function.Injective e →
      (∀ i, (e i).re ≤ ρ) →
      ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      ∀ (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) →
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ j' : Fin J, j ≤ j' →
              (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖c i j' y₁ k‖ ≤ C * y₁ ^ (ρ + δ))) →
            ∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
              ∀ (j' : Fin J), j ≤ j' → ∀ (y₁ : ℝ), 0 < y₁ → c i j' y₁ g₀ = 0 := by sorry
