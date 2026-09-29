-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/af01a814-a299-55d9-86e3-46c232485c17
-- title:
--   Flatness climbs the logarithmic chain (first ratio)
-- statement:
--   Fix a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$, and natural numbers $N_2,N_3$ with coefficient families $a_2:\mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3:\mathrm{Fin}(N_3+1)\to\mathbb{C}$ whose top coefficients are $1$. The assertion is: for every real $\rho$, every $n,J\in\mathbb{N}$, every injective $e:\mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re}e_i\le\rho$ for all $i$, every $\delta>0$, every $N\in\mathbb{N}$ and every $u:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ subject to the automorphy package — all iterated archimedean directional derivatives `WhittakerBlock.archDeriv` along arbitrary words in $\mathrm{Fin}\,3\times\mathrm{Fin}\,3$ are continuous; $u$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL`; $u(zg)=\omega(z)u(g)$ for adelic central scalars; [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ where $\det e\neq0$; finiteness of right type, namely a finite set $s$ of functions whose $\mathbb{C}$-span contains $g\mapsto u(gk)$ for every $k$ with all finite components $1$ and archimedean component in `orth3` ($k^{\mathsf T}k=1$); the two Casimir relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}=\sum_{i,j}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{ji}$ and $\mathrm{casimir3}$ is the corresponding triple sum; and moderate growth $\|(\text{word of archDeriv's applied to }u)(g)\|\le C\,\mathrm{gauge3}(g)^N$ — the following holds. Let $c:\mathrm{Fin}\,n\to\mathrm{Fin}\,J\to\mathbb{R}\to\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous in $(y_2,k)$ on $\{y_2>0\}$ and suppose that on every compact set $K$ of translates and every band $b^{-1}\le y_2\le b$ ($b\ge1$) there is $C$ with $$\Big\|\mathrm{whittaker3}(\mathrm{pins},\psi_\mathbb{Q},u)\big(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\big)-\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\Big\|\le C\,y_1^{\rho+\delta}$$ for $0<y_1\le1$, $k\in K$, where $\mathrm{whittaker3}$ is the triple integral of $u(\mathrm{upperUnipotent3}(x,y,z)g)\psi_\mathbb{Q}(-(x+y))$ against the additive adelic Haar measure conditioned on the adelic box (the pins being `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`). Then for any indices $i,j$: if $c_{ij}$ is flat, meaning that for each compact $K$ there is $C$ with $\|c_{ij}(y_2,k)\|\le C\,y_2^{\rho+\delta}$ for all $k\in K$ and $0<y_2\le1$, then the same flatness bound holds for $c_{ij'}$ for every $j'\ge j$.
--
--   This is the inductive step showing that flatness in the second torus ratio $y_2$ propagates from one logarithmic level to all higher levels of the asymptotic expansion of a $\mathrm{GL}_3$ Whittaker function in the first ratio $y_1$, the expansion being of the classical exponent–logarithm type for matrix coefficients of moderate growth. It feeds the threshold argument [`LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations), which extracts non-vanishing of a leading Whittaker coefficient in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∀ ρ : ℝ, ∀ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ → Function.Injective e →
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
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j y₂ k‖ ≤ C * y₂ ^ (ρ + δ)) →
            ∀ (j' : Fin J), j ≤ j' →
              (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ)) := by sorry
