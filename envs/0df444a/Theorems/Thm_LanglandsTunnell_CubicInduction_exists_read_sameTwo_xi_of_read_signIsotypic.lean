-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_read_sameTwo_xi_of_read_signIsotypic
-- name    : LanglandsTunnell.CubicInduction.exists_read_sameTwo_xi_of_read_signIsotypic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b45d14ca-6e9f-5f08-9f37-f90846147069
-- title:
--   Degree-two transition preserves readability from a sign-isotypic space
-- statement:
--   Fix $\nu\in\mathbb{C}^3$, scalars $\lambda_1,\lambda_2,\lambda_3\in\mathbb{C}$, a sign vector $\varepsilon\in(\mathbb{Z}/2)^3$, two $\mathbb{C}$-submodules $V,V_\varepsilon$ of the space of functions $GL_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$, and $k_1\in GL_3(\mathbb{A}_{\mathbb{Q}})$ whose archimedean component is $1$. The hypothesis on $V_\varepsilon$ has eight clauses: every $G\in V_\varepsilon$ is continuous; every $G$ satisfies `IsArchSmooth3` (for each $g$ the map $e\mapsto G(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e\neq 0\}$) and is an eigenfunction of the three operators $\sum_i\partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ built from the archimedean flow derivatives, with eigenvalues $\lambda_1,\lambda_2,\lambda_3$; every $G$ transforms on the left under upper-triangular real matrices $t$ with positive diagonal by $\prod_a t_{aa}^{\nu_a+(1,0,-1)_a}$; $V_\varepsilon$ is stable under right translation by elements trivial at all finite places with archimedean component $k$ satisfying $k^{\mathsf T}k=1$; each $G$ has all such right translates in the span of one finite set; $V_\varepsilon$ contains, for each $G$ and each pair $(c_0,d_0)$, a function $G'$ giving the derivative at $0$ of $s\mapsto G(g\cdot\mathrm{archRealLift3}(1+sE_{c_0d_0}))$; each $G$ satisfies $G(\mathrm{diag}((-1)^{\sigma_a})g)=(-1)^{\sum_a\varepsilon_a\sigma_a}G(g)$; and each $G$ is the $\varepsilon$-sign average $\tfrac18\sum_\sigma(-1)^{\sum_a\varepsilon_a\sigma_a}F(\mathrm{diag}((-1)^{\sigma_a})g)$ of some $F\in V$. Let $p$ be homogeneous of degree $2$ in three variables with $\sum_i\partial_i^2p=0$, and let $G\in V_\varepsilon$ read $p$ with exponent $\alpha=(2+\sum_a\varepsilon_a)\bmod 2$, i.e. $\det(o)^{\alpha}\,p(o_{00},o_{10},o_{20})=G(\mathrm{archRealLift3}\,o\cdot k_1)$ for every real $o$ with $\sum_a o_{ai}o_{aj}=\delta_{ij}$. With $\Xi\,\nu\,p$ the matrix whose $(c,c)$ entry is $2(\nu_c+(1,0,-1)_c)p$ and whose $(c,d)$ entry for $c\neq d$ is $-(X_{\max(c,d)}\partial_{\min(c,d)}p-X_{\min(c,d)}\partial_{\max(c,d)}p)$, and with $\mathrm{same}_2(M)=6\,S-(\sum_iX_i^2)\sum_i\partial_i^2S$ where $S=\sum_{c,d}X_c\,\partial_d(M_{cd})$, the conclusion is that some $G'\in V_\varepsilon$ reads $\mathrm{same}_2(\Xi\,\nu\,p)$ with the same exponent $\alpha$.
--
--   This is the same-degree step of the compact-picture transition calculus for the degree-two (harmonic quadric) case: the polynomial $\mathrm{same}_2(\Xi\,\nu\,p)$ produced by the induced-picture action on a harmonic quadric is again realised as the restriction to the orthogonal group of a member of the sign-isotypic space $V_\varepsilon$, with unchanged determinant twist. It feeds `exists_transitionStable_family_of_signIsotypic_submodule`, which assembles a transition-stable family of read polynomials in the analysis of the archimedean constituents entering the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_read_sameTwo_xi_of_read_signIsotypic.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_read_sameTwo_xi_of_read_signIsotypic
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (ε : Fin 3 → Fin 2) (V Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hVε : (∀ G ∈ Vε, Continuous G) ∧
      (∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) ∧
      (∀ G ∈ Vε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)))
    (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 2)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ Vε)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((2 + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
        G (WhittakerBlock.archRealLift3 o * k₁)) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((2 + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (same₂ (Ξ ν p))) =
        G' (WhittakerBlock.archRealLift3 o * k₁) := by sorry
