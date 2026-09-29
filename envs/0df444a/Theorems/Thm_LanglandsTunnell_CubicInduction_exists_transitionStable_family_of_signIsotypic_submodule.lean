-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_family_of_signIsotypic_submodule
-- name    : LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/fa0d289d-ae2d-51ae-89fe-6412a9ad4b95
-- title:
--   Transition-stable family of harmonic polynomials read on O(3)
-- statement:
--   Fix $\nu \in \mathbb{C}^3$, scalars $\lambda_1,\lambda_2,\lambda_3 \in \mathbb{C}$, a sign index $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, two $\mathbb{C}$-submodules $V, V_\varepsilon$ of the space of complex functions on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$, and $k_1$ in that group whose archimedean component is $1$. Assume the eight-clause package $hV_\varepsilon$: each $G \in V_\varepsilon$ is continuous; each $G$ is smooth in the archimedean variable (the map $e \mapsto G(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det \ne 0\}$ for every $g$) and satisfies $\mathrm{casimir}_1 G = \lambda_1 G$, $\mathrm{casimir}_2 G = \lambda_2 G$, $\mathrm{casimir}_3 G = \lambda_3 G$, where these are the sums $\sum_i \partial_{ii}$, $\sum_{i,j}\partial_{ij}\partial_{ji}$, $\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ of the one-parameter archimedean right derivatives; each $G$ transforms on the left under real matrices $t$ with vanishing entries below the diagonal and positive diagonal by $G(t\,g) = \big(\prod_a t_{aa}^{\,\nu_a + \rho_a}\big)G(g)$ with $\rho = (1,0,-1)$; $V_\varepsilon$ is stable under right translation by elements trivial at every finite place whose archimedean component $k$ satisfies $k^{\mathsf T}k = 1$, and for each $G$ all such translates lie in the span of one finite set; for each $G$ and each pair $(c_0,d_0)$ there is $G' \in V_\varepsilon$ with $s \mapsto G(g\cdot(1 + sE_{c_0 d_0}))$ differentiable at $0$ with derivative $G'(g)$, for all $g$; each $G$ satisfies $G(\mathrm{diag}((-1)^{\sigma_a})\,g) = (-1)^{\sum_a \varepsilon_a \sigma_a}G(g)$; and each $G$ is the $\varepsilon$-sign average $\tfrac18\sum_\sigma (-1)^{\sum_a \varepsilon_a\sigma_a}F(\mathrm{diag}((-1)^{\sigma_a})\,g)$ of some $F \in V$. Let $\Xi(\nu,p)$ be the $3\times3$ matrix of polynomials with diagonal entries $2(\nu_c+\rho_c)p$ and off-diagonal entries $-(X_{\max(c,d)}\partial_{\min(c,d)}p - X_{\min(c,d)}\partial_{\max(c,d)}p)$, and let $\mathrm{lower}_2$, $\mathrm{lower}_1$, $\mathrm{same}_2$ be the three explicit differential operators on such matrices written in the statement. The conclusion asserts the existence of $S : \mathbb{N} \to$ submodules of $\mathbb{C}[X_0,X_1,X_2]$ such that: every $p \in S\,\ell$ is homogeneous of degree $\ell$ and harmonic, $\sum_i \partial_i^2 p = 0$; each $p \in S\,\ell$ satisfies $p((-1)^{\sigma_a}X_a) = (-1)^{\sum_a(\varepsilon_a + \ell + \sum_b \varepsilon_b)\sigma_a}p$; $\mathrm{lower}_2(\Xi(\nu,p)) \in S(\ell-2)$ and $\mathrm{lower}_1(\Xi(\nu,p)) \in S(\ell-1)$ (truncated subtraction), and $\mathrm{same}_2(\Xi(\nu,p)) \in S\,2$ for $p \in S\,2$; for each $\ell$ and $p \in S\,\ell$ there is $G \in V_\varepsilon$ with $\det(o)^{(\ell + \sum_a \varepsilon_a)\bmod 2}\,p(o_{00},o_{10},o_{20}) = G(o\cdot k_1)$ for every real $o$ with $\sum_a o_{ai}o_{aj} = \delta_{ij}$; and if some $G \in V_\varepsilon$ is non-zero at some such $o\cdot k_1$, then $S\,\ell \ne \bot$ for some $\ell$.
--
--   This is the passage from an archimedean sign-isotypic space of adelic functions to the induced (compact) picture: the functions in $V_\varepsilon$ are read on the orthogonal matrices as determinant-twisted first-column realisations of harmonic homogeneous polynomials, and the resulting graded family is stable under the lowering and transition operators built from $\Xi(\nu,\cdot)$. It is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top) and by [`LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package`](thm.html#LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package), and is the uniform form, in $\varepsilon$ and $\nu$, of the separate transition-stable-family statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_transitionStable_family_of_signIsotypic_submodule.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule
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
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g))) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    ∃ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) ∧
      (∀ p ∈ S 2, same₂ (Ξ ν p) ∈ S 2) ∧
      (∀ ℓ, ∀ p ∈ S ℓ, ∃ G ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
            (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
          G (WhittakerBlock.archRealLift3 o * k₁)) ∧
      ((∃ G ∈ Vε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) → ∃ ℓ, S ℓ ≠ ⊥) := by sorry
