-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_firstRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.firstRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/99e9bf38-4111-5b9d-a7ad-181f28260513
-- title:
--   From orthogonal to all translates for a leading Whittaker coefficient
-- statement:
--   Fix a homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ and two monic complex coefficient families $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ (monic in the sense $a_2(N_2)=a_3(N_3)=1$). Then for every real $\rho$, naturals $n,J,N$, injective $e : \mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re}e_i\le\rho$ for all $i$, every $\delta>0$, and every $u : \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ satisfying: all iterated archimedean derivatives $\mathrm{archDeriv}\,i\,j\,\varphi\,(g)=\tfrac{d}{ds}\varphi(g\cdot(1+sE_{ij}))|_{s=0}$ of $u$ along arbitrary words in the directions $(i,j)$ are continuous; $u$ is left invariant under $\mathrm{GL}_3(\mathbb{Q})$ embedded by `globalPointsGL`; $u(zg)=\omega(z)u(g)$ for adelic central scalars $z$; `IsArchSmooth3 u`, i.e. $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det\neq 0\}$ for each $g$; there is a finite set $s$ of functions whose $\mathbb{C}$-span contains $g\mapsto u(gk)$ for every $k$ with trivial component at each finite place and archimedean component in $\mathrm{orth3}=\{k: k^{\mathsf T}k=1\}$; the two differential relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}\,i\,j(\mathrm{archDeriv}\,j\,i\,\varphi)$ and $\mathrm{casimir3}$ is the corresponding triple sum; and moderate growth $\|\text{(word derivative of }u)(g)\|\le C\,\mathrm{gauge3}(g)^N$ for each word: the following holds. Let $c : \mathrm{Fin}\,n\to\mathrm{Fin}\,J\to\mathbb{R}\to\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be functions, each $c\,i\,j$ continuous on $\{(y_2,k): y_2>0\}$, such that for every compact $K$ and every $b\ge 1$ there is $C$ with $$\Big\|W(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k)-\sum_{i,j}c\,i\,j\,y_2\,k\cdot y_1^{e_i}(\log y_1)^{j}\Big\|\le C\,y_1^{\rho+\delta}$$ for all $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le 1$, where $W$ is the Whittaker integral $\mathrm{whittaker3}$ of $u$ against the standard additive character $\psi_\mathbb{Q}$, formed with the carrier pins $\mathrm{productionPinsOf}\,\mathbb{Q}\,\emptyset\,(\lambda\_.\bot)\,(\lambda\_.1)$ on the adelic box, i.e. the triple integral of $u(\mathrm{upperUnipotent3}(x,y,z)g)\psi_\mathbb{Q}(-(x+y))$ against the conditioned adelic additive Haar measure. Then for all $i,j$: if $c\,i''\,j''\,y_2\,k=0$ whenever $\operatorname{Re}e_{i''}<\operatorname{Re}e_i$, $y_2>0$ and $k$ arbitrary, and if $c\,i\,j'\,y_2\,g_0=0$ for all $j'\ge j$, all $y_2>0$ and all $g_0$ whose archimedean component lies in $\mathrm{orth3}$, then $c\,i\,j\,y_2\,k=0$ for every $k$ and every $y_2>0$.
--
--   This is the propagation step for the leading exponent in the asymptotic expansion of a $\mathrm{GL}_3$ Whittaker function along the first diagonal ratio: vanishing of a coefficient at translates with orthogonal archimedean component is upgraded, using the Iwasawa decomposition at the infinite place together with the unipotent equivariance of the Whittaker integral, to vanishing at all translates. It is used by [`LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations`](thm.html#LanglandsTunnell.CubicInduction.exists_threshold_firstRatioCoeff_eq_zero_of_forall_secondRatioCoeff_eq_zero_of_casimir_relations) in the analytic input to the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_firstRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.firstRatioCoeff_eq_zero_of_forall_orth_eq_zero_of_leading_of_casimir_relations
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
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
              ∀ (j' : Fin J), j ≤ j' → ∀ (y₂ : ℝ), 0 < y₂ → c i j' y₂ g₀ = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0 := by sorry
