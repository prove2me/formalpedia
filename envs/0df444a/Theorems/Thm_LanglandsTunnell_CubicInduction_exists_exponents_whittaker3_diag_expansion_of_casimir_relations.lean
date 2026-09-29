-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_expansion_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_expansion_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8e2b8124-0664-58ff-852b-9bc4e22a094c
-- title:
--   Whittaker expansion on GL₃ from two Casimir relations
-- statement:
--   Fix a homomorphism $\omega$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^\times$ to $\mathbb{C}^\times$, natural numbers $N_2,N_3$ and coefficient vectors $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$, $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ with $a_2(N_2)=a_3(N_3)=1$. The assertion is that for every real $\rho$ there are $n,J\in\mathbb{N}$, exponents $e:\mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re}e_i\le\rho$, and $\delta>0$ — all independent of what follows — such that for every $N\in\mathbb{N}$ and every $u:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ subject to: every iterated archimedean derivative $\mathrm{archDeriv}$ along a word in $(\mathrm{Fin}\,3)^2$ (each step the $s$-derivative at $0$ of $g\mapsto\varphi(g\cdot\mathrm{archRealLift3}(1+sE_{ij}))$) is continuous; $u(\gamma g)=u(g)$ for $\gamma\in\mathrm{GL}_3(\mathbb{Q})$ embedded entrywise; $u(zI_3\,g)=\omega(z)u(g)$; `IsArchSmooth3 u`, i.e. $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det\neq0\}$ for each $g$; the right translates $g\mapsto u(gk)$, for $k$ trivial at every finite place and with archimedean component satisfying $k^{\mathsf T}k=1$, span a finite-dimensional space; $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{ji}\varphi$ and $\mathrm{casimir3}\,\varphi=\sum_{i,j,k}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{jk}\mathrm{archDeriv}_{ki}\varphi$; and each iterated derivative bounded by a constant times $\mathrm{gauge3}(g)^N$ — the Whittaker coefficient $W_u(g)=\iiint u(n(x,y,z)g)\psi_{\mathbb{Q}}(-(x+y))$, integrated against the adelic Haar measure conditioned on the standard adelic box, satisfies two expansions. First, there are functions $c_{ij}:\mathbb{R}\times\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$, continuous on $\{y>0\}$, such that for every compact $K$ and every $b\ge1$ there is $C$ with $\bigl\|W_u(\mathrm{diag}(y_1y_2,y_2,1)k)-\sum_{i,j}c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\bigr\|\le C\,y_1^{\rho+\delta}$ for all $k\in K$, $y_2\in[b^{-1},b]$ and $0<y_1\le1$, the diagonal matrix being inserted through $\mathrm{archRealLift3}$; second, the same statement with the roles of $y_1$ and $y_2$ interchanged.
--
--   This is the regular-singular asymptotic expansion of a $\mathrm{GL}_3$ Whittaker coefficient along each of the two simple-root directions of the diagonal torus: the exponents and the gain $\delta$ depend only on the central character, the two monic Casimir relations and the cut-off $\rho$, and are uniform in the form $u$ and in its growth exponent $N$. It feeds the derivation of a positive ray order, and hence of decay of Whittaker functions, in the cubic induction block used for the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_expansion_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_expansion_of_casimir_relations
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∀ ρ : ℝ, ∃ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ ∧ (∀ i, (e i).re ≤ ρ) ∧
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
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) := by sorry
