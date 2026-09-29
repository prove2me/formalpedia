-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/9f9c2abc-21ed-5290-b0a7-d23dc6057dea
-- title:
--   Flat regular-singular system for leading GL₃ Whittaker coefficients
-- statement:
--   Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$, and let $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ be monic, i.e. $a_2(N_2)=a_3(N_3)=1$. The assertion is that there is a threshold $\rho_0\in\mathbb{R}$, depending on these data only, such that for every $\rho\ge\rho_0$, all $n,J\in\mathbb{N}$, every injective $e:\mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re}e_i\le\rho$ for all $i$, every $\delta>0$, every $N$ and every $u:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ subject to the following: every iterated word of the archimedean derivations $\mathrm{archDeriv}\,i\,j\,\varphi(g)=\frac{d}{ds}\varphi(g\cdot\mathrm{archRealLift3}(1+sE_{ij}))|_{s=0}$ applied to $u$ is continuous; $u$ is invariant under left translation by the image of $\mathrm{GL}_3(\mathbb{Q})$; $u(z\cdot g)=\omega(z)u(g)$ for central adelic scalars $z$; $u$ is archimedean-smooth, i.e. $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det\ne 0\}$ for each $g$; there is a finite set $s$ of functions such that $g\mapsto u(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ with all finite components $1$ and archimedean component in $\mathrm{orth3}=\{k:k^{\mathrm T}k=1\}$; the two Casimir relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$ hold, where $\mathrm{casimir2}=\sum_{i,j}\mathrm{archDeriv}\,i\,j\circ\mathrm{archDeriv}\,j\,i$ and $\mathrm{casimir3}$ is the corresponding triple sum; and each derivative word of $u$ is bounded by $C\,\mathrm{gauge3}(g)^N$, with $\mathrm{gauge3}(g)=\max(1,\mathrm{archGauge3}(g)\,\mathrm{finGauge3}(g))$ — the following holds. Let $c_{ij}(y_2,k)$ be functions, each continuous on $\{y_2>0\}\times\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$, which provide an expansion of the Whittaker integral of $u$, taken with respect to the carrier pins $\mathrm{productionPinsOf}\,\mathbb{Q}\,\emptyset\,(\lambda\_.\bot)\,(\lambda\_.1)$ on the adelic box and the standard character $\psi_\mathbb{Q}$, in the first diagonal ratio: for every compact $K$ and every $b\ge1$ there is $C$ with $$\Bigl\|W\bigl(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\bigr)-\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j\Bigr\|\le C\,y_1^{\rho+\delta}$$ for $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le1$. Suppose further that $i$ is leading, in the sense that $c_{i''j''}(y_2,k)=0$ for all $k$, all $y_2>0$ and all $i''$ with $\operatorname{Re}e_{i''}<\operatorname{Re}e_i$, and that for every $j'\ge j$ the coefficient $c_{ij'}$ is flat of order $\rho+\delta$ in $y_2$ on compacta: for each compact $K$ there is $C$ with $\|c_{ij'}(y_2,k)\|\le C\,y_2^{\rho+\delta}$ for $k\in K$ and $0<y_2\le1$. Then for every $g_0$ whose archimedean component lies in $\mathrm{orth3}$, every $j'\ge j$ and every $Z\ge1$ there exist $R,d\in\mathbb{N}$, a matrix $M\in M_R(\mathbb{C})$, continuous linear operators $A_0,\dots,A_{d-1}$ on $\mathbb{C}^R$, a polynomial $q$, reals $\sigma,B$, functions $V,V':\mathbb{R}\to\mathbb{C}^R$ and an index $a_0$ such that $q\ne0$, $q(M)=0$, every root of $q$ has real part $<\sigma$, and on $(0,1]$: $V$ is differentiable with derivative $V'(s)$ satisfying $s\,V'(s)=M\,V(s)+\sum_{k<d}s^{k+1}A_k(V(s))$, $\|V(s)\|\le B\,s^{\sigma}$, and the $a_0$-th coordinate of $V(s)$ equals $c_{ij'}(Zs,g_0)$.
--
--   This is the step that folds the expansion of a Whittaker function on $\mathrm{GL}_3$ in the first diagonal ratio into a holonomic system in the second ratio at a leading exponent, producing for each flat coefficient function a coordinate of a solution of a regular-singular system with bounded tail terms and with exponents controlled by a single annihilating polynomial. It is used by `exists_threshold_firstRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations`, where the growth bound $\|V(s)\|\le B s^\sigma$ together with the root condition on $q$ forces the coefficient to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
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
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ j' : Fin J, j ≤ j' →
              (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ))) →
            ∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
              ∀ (j' : Fin J), j ≤ j' → ∀ (Z : ℝ), 1 ≤ Z →
                ∃ (R d : ℕ) (Mm : Matrix (Fin R) (Fin R) ℂ) (A : Fin d → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
                  (q : Polynomial ℂ) (σ B : ℝ) (V V' : ℝ → (Fin R → ℂ)) (a₀ : Fin R),
                  q ≠ 0 ∧ Polynomial.aeval Mm q = 0 ∧ (∀ x : ℂ, q.IsRoot x → x.re < σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt V (V' s) s ∧
                    (s : ℂ) • V' s = (fun a => ∑ b, Mm a b • V s b) +
                      ∑ k : Fin d, ((s : ℂ) ^ ((k : ℕ) + 1)) • A k (V s)) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖V s‖ ≤ B * s ^ σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, V s a₀ = c i j' (Z * s) g₀) := by sorry
