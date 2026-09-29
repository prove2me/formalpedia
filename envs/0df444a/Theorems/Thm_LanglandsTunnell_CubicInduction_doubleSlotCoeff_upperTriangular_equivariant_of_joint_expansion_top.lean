-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
-- name    : LanglandsTunnell.CubicInduction.doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7018fe2f-4684-5592-a357-f0aca1c34bf3
-- title:
--   Borel equivariance of the top-logarithmic double Whittaker coefficient
-- statement:
--   Fix a homomorphism $\omega$ from the idele class group units $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ and a function $u$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ subject to: every iterated archimedean derivative of $u$ along a word of matrix entries $(i,j)$, each step being $\varphi \mapsto \bigl(g \mapsto \tfrac{d}{ds}\varphi(g\cdot(1+sE_{ij})_\infty)|_{s=0}\bigr)$, is continuous; $u$ is invariant under left translation by $\mathrm{GL}_3(\mathbb{Q})$; central scalars $z$ act by $\omega(z)$; [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) holds, i.e. for each $g$ the map $e \mapsto u(g\cdot e_\infty)$ is $C^\infty$ on real $3\times 3$ matrices of nonzero determinant; and $\sum_i \partial_{ii} u = c_1 u$. Let $e : \mathrm{Fin}\,n \to \mathbb{C}$ be injective with $\operatorname{Re} e_i < \tau$ for all $i$. Assume two layers of asymptotics, uniform over compacta: for the Whittaker integral $W(g)=\int\!\!\int\!\!\int u(n(x,y,z)g)\psi_{\mathbb{Q}}(-(x+y))$, taken against the adelic additive Haar measure conditioned on the adelic box and with $n(x,y,z)$ the upper unipotent matrix, one has $W(\mathrm{diag}(y_1y_2,y_2,1)_\infty k)=\sum_{i,j} c_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j + O(y_1^{\tau})$ for $0<y_1\le 1$ and $y_2$ in any fixed band, with each $c_{ij}$ continuous on $\{y_2>0\}\times \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, and $c_{ij}(y_2,k)=\sum_{i',j'} c'_{ij,i'j'}(k)\,y_2^{e_{i'}}(\log y_2)^{j'}+O(y_2^{\tau})$ for $0<y_2\le1$ with each $c'_{ij,i'j'}$ continuous. Fix indices $i_0,i_0'$ and logarithmic powers $j_0,j_0'$ such that $c_{ij}$ vanishes whenever $\operatorname{Re} e_i<\operatorname{Re} e_{i_0}$, $c'_{i_0j_0,i'j'}$ vanishes whenever $\operatorname{Re} e_{i'}<\operatorname{Re} e_{i_0'}$, $c_{i_0 j}$ vanishes for $j>j_0$, and $c'_{i_0j_0,i_0'j'}$ vanishes for $j'>j_0'$. The conclusion is that for every upper-triangular real matrix $t$ with positive diagonal entries and every $g$, $$c'_{i_0j_0,i_0'j_0'}(t_\infty g)=\Bigl(\prod_{a} t_{aa}^{\,\nu_a+\rho_a}\Bigr) c'_{i_0j_0,i_0'j_0'}(g),$$ where $\nu=(e_{i_0}-1,\; e_{i_0'}-e_{i_0},\; c_1-e_{i_0'}+1)$ and $\rho=(1,0,-1)$.
--
--   This is the $\mathrm{GL}_3$ statement that the double leading coefficient of the asymptotic expansion of a Whittaker function, taken at the lowest exponent in each of the two successive degenerations but at the highest logarithmic power occurring there, transforms by a fixed quasicharacter of the Borel subgroup, i.e. is a principal-series vector with parameter $\nu+\rho$; it is the variant requiring no log-free assumption, so it applies at repeated indicial roots. It feeds the construction of the induced-picture package and the dichotomy for leading coefficients of smoothing submodules used in the cubic-induction step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (c₁ : ℂ) (hc₁ : WhittakerBlock.casimir1 u = c₁ • u)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (τ : ℝ) (hτ : ∀ i, (e i).re < τ)
    (cf : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcf : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cf i j p.1 p.2) {p | 0 < p.1})
    (hexp₁ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ u
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        (∑ i : Fin n, ∑ j : Fin J, cf i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
      C * y₁ ^ τ)
    (cf' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcf' : ∀ i j i' j', Continuous (cf' i j i' j'))
    (hexp₂ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
      ‖cf i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cf' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
        C * y₂ ^ τ)
    (i₀ i₀' : Fin n) (j₀ j₀' : Fin J)
    (hbot₁ : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i₀).re → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i j y₂ k = 0)
    (hbot₂ : ∀ (i' : Fin n) (j' : Fin J), (e i').re < (e i₀').re → ∀ k, cf' i₀ j₀ i' j' k = 0)
    (htop₁ : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i₀ j y₂ k = 0)
    (htop₂ : ∀ j' : Fin J, (j₀' : ℕ) < (j' : ℕ) → ∀ k, cf' i₀ j₀ i₀' j' k = 0) :
    ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        cf' i₀ j₀ i₀' j₀' (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^
            ((![e i₀ - 1, e i₀' - e i₀, c₁ - e i₀' + 1] : Fin 3 → ℂ) a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
          cf' i₀ j₀ i₀' j₀' g := by sorry
