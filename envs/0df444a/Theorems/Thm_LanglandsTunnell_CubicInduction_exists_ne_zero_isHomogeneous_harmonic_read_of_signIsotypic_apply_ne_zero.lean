-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/5bd16180-3467-5c46-99c1-69290f8eabae
-- title:
--   A non-zero harmonic polynomial read from a sign-isotypic space
-- statement:
--   Fix $\nu:\mathrm{Fin}\,3\to\mathbb C$, scalars $\lambda_1,\lambda_2,\lambda_3\in\mathbb C$, a sign character $\varepsilon:\mathrm{Fin}\,3\to\mathbb Z/2$, two $\mathbb C$-submodules $V,V_\varepsilon$ of the space of functions $GL_3(\mathbb A_{\mathbb Q})\to\mathbb C$, and $k_1\in GL_3(\mathbb A_{\mathbb Q})$ whose archimedean component is $1$. Assume of $V_\varepsilon$ the eight clauses: each $G\in V_\varepsilon$ is continuous; each $G$ satisfies [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. $e\mapsto G(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on real matrices of non-zero determinant, and is an eigenfunction of `casimir1`, `casimir2`, `casimir3` (the first, second and third traces of the right-derivative operators $\mathrm{archDeriv}$) with eigenvalues $\lambda_1,\lambda_2,\lambda_3$; each $G$ transforms by $\prod_a (t_{aa})^{\nu_a+(1,0,-1)_a}$ under left translation by upper-triangular $t$ with positive diagonal; right translation by elements trivial at all finite places whose archimedean component lies in $\mathrm{orth3}$ ($k^{\mathsf T}k=1$) preserves $V_\varepsilon$, and all such translates of a fixed $G$ span a finite-dimensional space; the nine one-parameter flows $s\mapsto G(g\cdot\mathrm{archRealLift3}(1+sE_{c_0d_0}))$ are differentiable at $0$ with derivative again in $V_\varepsilon$; left translation by $\mathrm{diag}((-1)^{\sigma_a})$ multiplies $G$ by $(-1)^{\sum_a\varepsilon_a\sigma_a}$; and each $G$ is the $\varepsilon$-sign average $\tfrac18\sum_\sigma(-1)^{\sum_a\varepsilon_a\sigma_a}F(\mathrm{diag}((-1)^{\sigma_a})\,\cdot\,)$ of some $F\in V$. Assume further that some $G\in V_\varepsilon$ is non-zero at $\mathrm{archRealLift3}(o)\,k_1$ for some real $o$ with $o^{\mathsf T}o=1$. Then there exist $\ell\in\mathbb N$ and a non-zero $p\in\mathbb C[X_0,X_1,X_2]$, homogeneous of degree $\ell$ and harmonic ($\sum_i\partial_i^2p=0$), together with $G'\in V_\varepsilon$ such that for every real orthogonal $o$, $$\det(o)^{(\ell+\sum_a\varepsilon_a)\bmod 2}\,p(o_{00},o_{10},o_{20})=G'(\mathrm{archRealLift3}(o)\,k_1),$$ the left-hand evaluation being $p$ with its variables substituted by the first column of $o$.
--
--   This is the exhaustion step of the archimedean analysis: it extracts from a non-vanishing sign-isotypic automorphic vector a non-zero spherical harmonic of some degree $\ell$, realised on the orthogonal group through the first column and twisted by the determinant to the parity forced by $\ell$ and $\varepsilon$. It is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule) in the construction of the cubic induction needed for the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
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
    (hne : (∃ G ∈ Vε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0)) :
    ∃ (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧ p.IsHomogeneous ℓ ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
        G' (WhittakerBlock.archRealLift3 o * k₁) := by sorry
