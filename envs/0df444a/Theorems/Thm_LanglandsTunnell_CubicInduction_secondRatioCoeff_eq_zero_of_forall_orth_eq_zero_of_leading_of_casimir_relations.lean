-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_secondRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.secondRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/3e74a35e-9be1-5d15-ab0a-522b1503c289
-- title:
--   Leading Whittaker coefficient: from orthogonal translates to all translates
-- statement:
--   Fix a continuous-free datum: a homomorphism $\omega$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$, and two monic coefficient vectors $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ (so $a_2(N_2)=a_3(N_3)=1$). The assertion is then universally quantified over: a real $\rho$; naturals $n,J,N$; an injective $e : \mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re}e_i\le\rho$ for all $i$; a real $\delta>0$; and a function $u$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ subject to: every iterated archimedean directional derivative of $u$ along a word $w$ of matrix-unit directions, each $\mathrm{archDeriv}\,i\,j\,\varphi(g)=\frac{d}{ds}\varphi\bigl(g\cdot\mathrm{archRealLift3}(1+sE_{ij})\bigr)|_{s=0}$, is continuous and is bounded by $C\cdot\mathrm{gauge3}(g)^{N}$; left invariance of $u$ under the rational points $\mathrm{GL}_3(\mathbb{Q})$ embedded in the adelic group; $u(z\cdot 1\cdot g)=\omega(z)u(g)$ for ideles $z$; `IsArchSmooth3 u`, i.e. for each $g$ the map $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on $\{\det e\neq 0\}$; the existence of a finite set $s$ of functions spanning all right translates $g\mapsto u(gk)$ with $k$ trivial at every finite place and archimedean component in $\mathrm{orth3}=\{k : k^{\mathsf T}k=1\}$; and the two relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$, $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}\,i\,j(\mathrm{archDeriv}\,j\,i\,\varphi)$ and $\mathrm{casimir3}$ is the analogous triple sum. Further, it is quantified over a family $c_{ij}(y_1,k)$ of coefficient functions such that each $(y_1,k)\mapsto c_{ij}(y_1,k)$ is continuous on $\{y_1>0\}$ and such that, locally uniformly in $k$ over compacta and in $y_1$ over intervals $[b^{-1},b]$, the Whittaker integral $\mathrm{whittaker3}$ of $u$ — the triple integral of $u(\mathrm{upperUnipotent3}(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$ against the additive Haar measure conditioned to the adelic box — evaluated at $\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k$ differs from $\sum_{i,j}c_{ij}(y_1,k)\,y_2^{e_i}(\log y_2)^{j}$ by $O(y_2^{\rho+\delta})$ for $0<y_2\le 1$. The conclusion: for indices $i,j$ such that $c_{i''j''}$ vanishes identically (all translates, all $y_1>0$) whenever $\operatorname{Re}e_{i''}<\operatorname{Re}e_i$, and such that $c_{ij'}(y_1,g_0)=0$ for all $j'\ge j$, all $y_1>0$ and all $g_0$ whose archimedean component lies in $\mathrm{orth3}$, one has $c_{ij}(y_1,k)=0$ for every translate $k$ and every $y_1>0$.
--
--   This is the step in the analysis of the joint Whittaker expansion on $\mathrm{GL}_3$ in the second ratio variable that upgrades vanishing of a leading expansion coefficient from translates with orthogonal archimedean component to arbitrary adelic translates, the orthogonal case being reached through the archimedean Iwasawa decomposition. It is used in the derivation of a threshold for the vanishing of second-ratio coefficients, [`LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_of_forall_firstRatioCoeff_eq_zero_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_of_forall_firstRatioCoeff_eq_zero_of_casimir_relations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_secondRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.secondRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
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
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
              ∀ (j' : Fin J), j ≤ j' → ∀ (y₁ : ℝ), 0 < y₁ → c i j' y₁ g₀ = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0 := by sorry
