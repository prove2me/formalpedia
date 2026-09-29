-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_aeval_signTwist_eq_smul_of_read_signIsotypic
-- name    : LanglandsTunnell.CubicInduction.aeval_signTwist_eq_smul_of_read_signIsotypic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/91be20d0-6f27-5b1c-a7d4-d2b849afddc6
-- title:
--   Sign type of a polynomial read off a sign-isotypic space
-- statement:
--   Fix a triple $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$, scalars $\lambda_1,\lambda_2,\lambda_3 \in \mathbb{C}$, a sign character $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, two $\mathbb{C}$-submodules $V, V_\varepsilon$ of the space of functions $GL_3(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$, and an element $k_1$ of $GL_3(\mathbb{A}_\mathbb{Q})$ whose archimedean component `archComponent3` is $1$. The hypothesis on $V_\varepsilon$ is an eight-clause package: every $G \in V_\varepsilon$ is continuous; is smooth in the real coordinates at infinity (in the sense of [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), contradifferentiability of $e \mapsto G(g\cdot\text{archRealLift3}\,e)$ on the locus $\det \ne 0$) and is an eigenfunction of `casimir1`, `casimir2`, `casimir3`, the traces of one, two and three of the flow derivatives `archDeriv`, with eigenvalues $\lambda_1,\lambda_2,\lambda_3$; transforms under left translation by an upper triangular real matrix $t$ with positive diagonal by the factor $\prod_a t_{aa}^{\nu_a + (1,0,-1)_a}$; is stable under right translation by elements trivial at every finite place and archimedean component in `orth3` (the matrices $k$ with $k^{T}k = 1$); has all such right translates in the span of one finite set; admits, for each pair $(c_0,d_0)$, a member of $V_\varepsilon$ as derivative at $0$ of the corresponding one-parameter flow; satisfies $G(\mathrm{diag}((-1)^{\sigma_a})\cdot g) = (-1)^{\sum_a \varepsilon_a\sigma_a}G(g)$ for all $\sigma$; and equals the $\varepsilon$-sign projection $\tfrac18\sum_\sigma (-1)^{\sum_a \varepsilon_a \sigma_a} F(\mathrm{diag}((-1)^{\sigma_a})\cdot g)$ of some $F \in V$. Let $\ell \in \mathbb{N}$ and let $p \in \mathbb{C}[X_0,X_1,X_2]$ be homogeneous of degree $\ell$, and let $G \in V_\varepsilon$ satisfy: for every real $3\times 3$ matrix $o$ with orthonormal columns, $\det(o)^{(\ell + \sum_a \varepsilon_a)\bmod 2}\,p(o_{00},o_{10},o_{20}) = G(\text{archRealLift3}\,o \cdot k_1)$. The conclusion is that for every $\sigma : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ the substitution $X_a \mapsto (-1)^{\sigma_a}X_a$ sends $p$ to $(-1)^{\sum_a (\varepsilon_a + \ell + \sum_b \varepsilon_b)\sigma_a}\,p$, an identity of polynomials.
--
--   This identifies the type of a homogeneous polynomial under the group of diagonal sign matrices once the polynomial is read off, via first columns of orthogonal matrices, from a space of functions isotypic for the sign character $\varepsilon$: the polynomial has pure sign type $\chi_\varepsilon \cdot \det^{(\ell + \sum \varepsilon)\bmod 2}$, the elementary $M$-type bookkeeping for an induced representation of $O(3)$. It is used in the construction of a transition-stable family of such polynomials, in `exists_transitionStable_family_of_signIsotypic_submodule`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_aeval_signTwist_eq_smul_of_read_signIsotypic.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.aeval_signTwist_eq_smul_of_read_signIsotypic
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
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ Vε)
    (hread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
        G (WhittakerBlock.archRealLift3 o * k₁)) :
    ∀ σ : Fin 3 → Fin 2,
      MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
        MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p := by sorry
