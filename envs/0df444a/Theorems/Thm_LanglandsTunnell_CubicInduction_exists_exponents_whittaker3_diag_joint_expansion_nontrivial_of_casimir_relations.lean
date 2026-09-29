-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations
-- name    : LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/4bf53472-2b0e-5f19-bd13-e55ba471de13
-- title:
--   Joint two-variable Whittaker expansion with leading-slice non-triviality
-- statement:
--   Fix a character $\omega$ of the idele units of $\mathbb{Q}$ (a monoid homomorphism $(\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$) and two monic polynomial relations, given by coefficient families $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ with top coefficients $1$. The assertion is that there is a threshold $\rho_0\in\mathbb{R}$ such that for every $\rho\ge\rho_0$ one can choose $n,J\in\mathbb{N}$, pairwise distinct exponents $e : \mathrm{Fin}\,n\to\mathbb{C}$ with $\operatorname{Re} e_i\le\rho$, and $\delta>0$, with the following property for every $N\in\mathbb{N}$ and every $u : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ subject to: continuity of every iterated archimedean derivative word $\mathrm{archDeriv}$ applied to $u$ along a list of matrix entries; left invariance under the rational points $\mathrm{GL}_3(\mathbb{Q})$; the central transformation rule $u(zg)=\omega(z)u(g)$ for adelic scalars $z$; `IsArchSmooth3 u`, i.e. for each $g$ the map $e\mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ is $C^{\infty}$ on $\{\det\ne 0\}$; finiteness under the orthogonal group, in the form of a finite set $s$ of functions whose $\mathbb{C}$-span contains $g\mapsto u(gk)$ for every $k$ trivial at all finite places with archimedean component in $\mathrm{orth3}=\{k:k^{\mathsf T}k=1\}$; the two relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}u=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}u=0$, where $\mathrm{casimir2}\,\varphi=\sum_{i,j}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{ji}\varphi$ and $\mathrm{casimir3}\,\varphi=\sum_{i,j,k}\mathrm{archDeriv}_{ij}\mathrm{archDeriv}_{jk}\mathrm{archDeriv}_{ki}\varphi$; and polynomial growth, each derivative word of $u$ bounded by $C\cdot\mathrm{gauge3}(g)^N$. The conclusion is the conjunction of two mirror-image clauses. In the first, there are functions $c_{ij}(y,k)$, continuous on $\{y>0\}\times\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, such that for every compact $K$ and every $b\ge 1$ there is $C$ with $$\Big\|W u\big(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\big)-\sum_{i<n}\sum_{j<J}c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\Big\|\le C\,y_1^{\rho+\delta}$$ for $k\in K$, $b^{-1}\le y_2\le b$ and $0<y_1\le 1$, where $Wu$ is the Whittaker integral $\mathrm{whittaker3}$ of $u$ against the standard additive character $\mathrm{psiQ}$, taken with the carrier pins $\mathrm{productionPinsOf}$ built from empty $D$, trivial level subgroups, trivial generators and the adelic box; moreover there are continuous $c'_{iji'j'}$ with $\|c_{ij}(y_2,k)-\sum_{i',j'}c'_{iji'j'}(k)\,y_2^{e_{i'}}(\log y_2)^{j'}\|\le C y_2^{\rho+\delta}$ uniformly for $k$ in a compact set and $0<y_2\le 1$, and, in addition, the non-triviality clause: for each $(i,j)$, if $c_{i''j''}$ vanishes identically for all $i''$ with $\operatorname{Re}e_{i''}<\operatorname{Re}e_i$ and all $c'_{iji'j'}$ vanish identically, then $c_{ij}(y_2,k)=0$ for all $k$ and all $y_2>0$. The second clause is the same statement with the roles of $y_1$ and $y_2$ interchanged.
--
--   This is the two-variable regular-singular expansion of a $\mathrm{GL}_3$ Whittaker coefficient along the torus direction $\mathrm{diag}(y_1y_2,y_2,1)$, strengthened by the statement that a leading slice of the expansion whose secondary coefficients all vanish is itself zero, at the cost of replacing 'for all $\rho$' by 'for all $\rho$ beyond a threshold $\rho_0$ depending only on $\omega$ and the two central relations'. It feeds the analysis of leading coefficients and transition-stable families in the cubic induction used for the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_exponents_whittaker3_diag_joint_expansion_nontrivial_of_casimir_relations
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ ∧ Function.Injective e ∧ (∀ i, (e i).re ≤ ρ) ∧
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
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)) := by sorry
