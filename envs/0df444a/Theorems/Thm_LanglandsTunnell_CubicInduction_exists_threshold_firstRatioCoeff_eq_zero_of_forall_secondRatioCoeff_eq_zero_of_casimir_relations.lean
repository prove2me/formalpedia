-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/5110c036-3614-580f-b2e6-dcb0dbfba340
-- title:
--   Vanishing of a leading first-ratio Whittaker coefficient on GL₃
-- statement:
--   Fix a group homomorphism $\omega$ from the ideles $(\mathbb{A}_\mathbb{Q})^\times$ to $\mathbb{C}^\times$, natural numbers $N_2,N_3$ and coefficient families $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ that are monic, i.e. $a_2(N_2)=a_3(N_3)=1$. The assertion is that there exists a real threshold $\rho_0$ such that for every $\rho\ge\rho_0$, every $n,J\in\mathbb{N}$, every injective $e:\mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re} e_i\le\rho$ for all $i$, every $\delta>0$, every $N\in\mathbb{N}$ and every $u : \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ subject to: all iterated archimedean derivative words of $u$ (each `WhittakerBlock.archDeriv` $i\,j$ differentiating at $s=0$ along the one-parameter family $g\mapsto g\cdot\mathrm{archRealLift3}(1+sE_{ij})$) are continuous; $u$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$; $u(zg)=\omega(z)u(g)$ for central adelic scalars; $u$ is smooth in the archimedean matrix entries on the locus of nonvanishing determinant; the right translates $g\mapsto u(gk)$ over all $k$ trivial at every finite place with orthogonal archimedean component ($k^{\mathsf T}k=1$) span a finite-dimensional space; $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where the two Casimir operators are the second- and third-order sums of archimedean derivative words; and each derivative word of $u$ is bounded by $C\cdot\mathrm{gauge3}(g)^N$. Given further coefficient functions $c_{ij}(y_2,k)$, continuous on $\{y_2>0\}$, such that the Whittaker integral of $u$ for the standard additive character $\psi_\mathbb{Q}$ and the carrier data $\mathrm{productionPinsOf}\,\mathbb{Q}\,\emptyset\,\bot\,1\,(\text{adelic box})$, evaluated at $\mathrm{diag}(y_1y_2,y_2,1)\,k$, differs from $\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j$ by $O(y_1^{\rho+\delta})$ uniformly for $k$ in compacta and $y_2$ in bands $[b^{-1},b]$, and continuous functions $c'_{ij\,i'j'}(k)$ with $c_{ij}(y_2,k)-\sum_{i',j'}c'_{ij\,i'j'}(k)\,y_2^{e_{i'}}(\log y_2)^{j'}=O(y_2^{\rho+\delta})$ uniformly on compacta for $0<y_2\le1$: then for indices $i,j$ such that all $c_{i''j''}$ with $\operatorname{Re} e_{i''}<\operatorname{Re} e_i$ vanish identically and all $c'_{ij\,i'j'}$ vanish identically, one has $c_{ij}(y_2,k)=0$ for every $k$ and every $y_2>0$.
--
--   This is the non-triviality clause of the two-ratio asymptotic expansion of centre-finite Whittaker coefficients on $\mathrm{GL}_3$ over $\mathbb{Q}$, in the form with a uniform threshold $\rho_0$ depending only on the central character and the two monic Casimir relations: a coefficient of the first-ratio expansion that is leading (lower exponents absent) and whose own second-ratio coefficients all vanish must itself vanish. It is used by the construction of the joint expansion with non-trivial exponent data, so that the joint statement can be assembled from the plain expansion together with this clause for each ratio.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations
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
        ∀ (c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
          (∀ i j i' j', Continuous (c' i j i' j')) →
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) →
          ∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0 := by sorry
