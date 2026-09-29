-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_threshold_secondRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/a14fea12-fe24-5590-b09f-d88cf44ba5bf
-- title:
--   Flat regular–singular coefficient system at a leading exponent
-- statement:
--   Fix a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ and two monic coefficient vectors $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ (i.e. $a_2(N_2)=a_3(N_3)=1$). Then there is a threshold $\rho_0\in\mathbb{R}$ such that for every $\rho\ge\rho_0$ the following holds. Let $n,J\in\mathbb{N}$, let $e:\mathrm{Fin}\,n\to\mathbb{C}$ be injective with $\mathrm{Re}\,e_i\le\rho$ for all $i$, let $\delta>0$, let $N\in\mathbb{N}$ and let $u:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ satisfy: every iterated archimedean derivative word $\mathrm{archDeriv}\,i_1j_1\cdots$ applied to $u$ is continuous; $u$ is left invariant under the rational points $\mathrm{GL}_3(\mathbb{Q})$; $u(zg)=\omega(z)u(g)$ for central ideles $z$; `IsArchSmooth3 u`, that is $e\mapsto u(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ where $\det e\neq0$; the right translates $g\mapsto u(gk)$, for $k$ with all finite components trivial and archimedean component $k$ satisfying $k^{\mathsf T}k=1$, all lie in the $\mathbb{C}$-span of one finite set of functions; the two Casimir relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}\,i\,j(\mathrm{archDeriv}\,j\,i\,\varphi)$ and $\mathrm{casimir3}$ is the analogous triple sum; and moderate growth $\|(\text{word})u(g)\|\le C\,\mathrm{gauge3}(g)^N$ for each derivative word. Let $c_{ij}(y_1,k)$ be functions, continuous in $(y_1,k)$ on $\{y_1>0\}$, which expand the Whittaker integral $\mathrm{whittaker3}$ of $u$ (against the standard additive character $\psi_\mathbb{Q}$, with the unipotent integration taken for the adelic Haar measure conditioned to the adelic box) in the second ratio: for every compact $K$ and $b\ge1$ there is $C$ with $$\Big\|\mathrm{whittaker3}(u)\big(\mathrm{diag}(y_1y_2,y_2,1)k\big)-\sum_{i,j}c_{ij}(y_1,k)\,y_2^{e_i}(\log y_2)^{j}\Big\|\le C\,y_2^{\rho+\delta}$$ for $k\in K$, $b^{-1}\le y_1\le b$ and $0<y_2\le1$. Fix $i,j$ such that $i$ is leading, i.e. $c_{i''j''}(y_1,k)=0$ for all $k$, all $y_1>0$ and all $i''$ with $\mathrm{Re}\,e_{i''}<\mathrm{Re}\,e_i$, and such that $c_{ij'}$ is flat of order $\rho+\delta$ for every $j'\ge j$: for each compact $K$ there is $C$ with $\|c_{ij'}(y_1,k)\|\le C\,y_1^{\rho+\delta}$ for $k\in K$ and $0<y_1\le1$. Then for every $g_0$ whose archimedean component satisfies $k^{\mathsf T}k=1$, every $j'\ge j$ and every $Z\ge1$, there exist $R,d\in\mathbb{N}$, a matrix $M\in M_R(\mathbb{C})$, continuous linear operators $A_0,\dots,A_{d-1}$ on $\mathbb{C}^R$, a nonzero polynomial $q$ with $q(M)=0$ all of whose roots have real part $<\sigma$, reals $\sigma,B$, functions $V,V':(0,\infty)\to\mathbb{C}^R$ and an index $a_0\in\mathrm{Fin}\,R$ such that on $(0,1]$ the function $V$ is differentiable with derivative $V'$ and satisfies the regular–singular system $s\,V'(s)=M\,V(s)+\sum_{k<d}s^{k+1}A_k(V(s))$, the bound $\|V(s)\|\le B\,s^{\sigma}$ holds on $(0,1]$, and the $a_0$-th coordinate of $V(s)$ equals $c_{ij'}(Zs,g_0)$ for $s\in(0,1]$.
--
--   This is the step of the asymptotic analysis of Whittaker functions on $\mathrm{GL}_3$ in which the expansion in the second diagonal ratio is folded into the holonomic system governing the first ratio: at a leading exponent, the rescaled coefficient function $s\mapsto c_{ij'}(Zs,g_0)$ is realised as a coordinate of a solution of a regular–singular first-order system with a bound $O(s^\sigma)$ exceeding the real parts of all roots of the annihilating polynomial. It is used by [`LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_eq_zero_orth_of_flat_of_leading_of_casimir_relations), where the system forces the coefficient to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_threshold_secondRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_threshold_secondRatioCoeff_flat_regularSingular_system_of_leading_of_casimir_relations
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
              ∀ (j' : Fin J), j ≤ j' → ∀ (Z : ℝ), 1 ≤ Z →
                ∃ (R d : ℕ) (Mm : Matrix (Fin R) (Fin R) ℂ) (A : Fin d → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
                  (q : Polynomial ℂ) (σ B : ℝ) (V V' : ℝ → (Fin R → ℂ)) (a₀ : Fin R),
                  q ≠ 0 ∧ Polynomial.aeval Mm q = 0 ∧ (∀ x : ℂ, q.IsRoot x → x.re < σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt V (V' s) s ∧
                    (s : ℂ) • V' s = (fun a => ∑ b, Mm a b • V s b) +
                      ∑ k : Fin d, ((s : ℂ) ^ ((k : ℕ) + 1)) • A k (V s)) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖V s‖ ≤ B * s ^ σ) ∧
                  (∀ s ∈ Set.Ioc (0 : ℝ) 1, V s a₀ = c i j' (Z * s) g₀) := by sorry
