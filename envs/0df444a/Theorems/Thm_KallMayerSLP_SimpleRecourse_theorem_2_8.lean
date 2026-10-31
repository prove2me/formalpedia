-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_theorem_2_8
-- name    : KallMayerSLP.SimpleRecourse.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:01.92045+00:00
-- url     : https://prove2.me/theorems/e7da6727-20e7-4612-88dd-85b2837d8de2
-- title:
--   Theorem 2.8 — multiple simple recourse is simple recourse with the mixed distribution $G$
-- statement:
--   Let the constants $\alpha_k,\beta_k,u_k,l_k$ ($k=0,\dots,K-1$) and $\gamma$ satisfy Definition 2.4, and let $\tilde\xi$ be a real random variable with distribution function $F_{\tilde\xi}$ and finite mean. Let $G$ be the distribution function
--
--   $$
--   G(\xi)=\frac{\sum_{k=0}^{K-1}\alpha_kF_{\tilde\xi}(\xi+u_k)+\sum_{k=0}^{K-1}\beta_kF_{\tilde\xi}(\xi-l_k)}{\sum_{k=0}^{K-1}(\alpha_k+\beta_k)} \tag{2.62}
--   $$
--
--   and $C$ the constant
--
--   $$
--   C=\frac{\bigl(\sum_{k=0}^{K-1}\alpha_k\bigr)\sum_{k=0}^{K-1}\beta_kl_k+\bigl(\sum_{k=0}^{K-1}\beta_k\bigr)\sum_{k=0}^{K-1}\alpha_ku_k}{\sum_{k=0}^{K-1}(\alpha_k+\beta_k)}. \tag{2.63}
--   $$
--
--   Then:
--
--   1. $G$ is the distribution function of a probability measure on $\mathbb R$.
--   2. For every $z\in\mathbb R$
--   $$
--   \sum_{k=0}^{K-1}\alpha_k\int(\xi-z)^+\,dF_{\tilde\xi}(\xi+u_k)+\sum_{k=0}^{K-1}\beta_k\int(\xi-z)^-\,dF_{\tilde\xi}(\xi-l_k)=\Bigl(\sum_{k=0}^{K-1}\alpha_k\Bigr)\int(\xi-z)^+\,dG(\xi)+\Bigl(\sum_{k=0}^{K-1}\beta_k\Bigr)\int(\xi-z)^-\,dG(\xi)-C,
--   $$
--   that is, the expected MSRT function (2.60) equals the expected SRT function (2.61) with distribution $G$. The expected MSRT function $\Psi$ of Definition 2.4 equals the right-hand side minus $\gamma$.
--   3. Consequently, for any data $A,b,c,t$, a pair $(x,z)$ solves the multiple simple recourse problem (2.59) with the expected MSRT function if and only if it solves (2.59) with the expected SRT function (2.61).
--
--   A recourse constraint with stepwise increasing marginal costs can thus be handled by any method for simple recourse, at the price of replacing the distribution of $\tilde\xi$ by the mixture $G$.
--
--   **Formalization Note** $dF_{\tilde\xi}(\xi+u_k)$ is integration against the law of $\tilde\xi-u_k$, $dF_{\tilde\xi}(\xi-l_k)$ against that of $\tilde\xi+l_k$, and $dG$ against a probability measure $\nu$ with distribution function $G$. Such a $\nu$ exists (item 1) and is unique, and items 2–3 are stated for every such $\nu$.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
--   - reading: the sums in (2.61) printed as Σ_{k=k}^{K−1} → Σ_{k=0}^{K−1}; reason: typo; (2.62)–(2.63) and the derivation on p.241 (A = W_α = Σ_{k=0}^{K−1} α_k, B = W_β) use k = 0 (paper.md correction 3)
--   - encoding: ∫ … dF_ξ̃(ξ + u_k), ∫ … dF_ξ̃(ξ − l_k), ∫ … dG(ξ) → integrals against P.map (· − u k), P.map (· + l k), and any probability measure ν with cdf ν = G (whose existence is the first conjunct); reason: a Stieltjes integral against a distribution function is the integral against the unique probability measure it determines
--   - reading: the problem (2.59) with (2.60) is equivalent to the simple recourse problem with (2.61) → (2.60)(z) = (2.61)(z) for all z, Ψ(z) = (2.61)(z) − γ for the Ψ of Definition 2.4, and the same optimal solutions of (2.59) for all A, b, c, t; reason: the derivation on pp.239–241 proves the pointwise identity; the two objectives differ by the constant γ, so the problems have the same optimal solutions
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Theorem 2.8, (2.59)–(2.63), pp.241–242 (PDF 250–251)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsMSRTData
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedMSRT
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureCdf
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureConst
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsOptimal259

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Theorem 2.8 (van der Vlerk): multiple simple recourse is simple recourse with a mixed
distribution.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Theorem 2.8, p.242 (PDF 251).
The multiple simple recourse problem (2.59) with the expected MSRT function
`Ψ(z) = Σ_{k=0}^{K−1} α_k ∫ (ξ − z)⁺ dF_ξ̃(ξ + u_k) + Σ_{k=0}^{K−1} β_k ∫ (ξ − z)⁻ dF_ξ̃(ξ − l_k)` (2.60)
is equivalent to the simple recourse problem with the expected SRT function
`Ψ(z) = (Σ_{k=0}^{K−1} α_k) ∫ (ξ − z)⁺ dG(ξ) + (Σ_{k=0}^{K−1} β_k) ∫ (ξ − z)⁻ dG(ξ) − C` (2.61)
using the distribution function `G` of (2.62) and the constant `C` of (2.63).

Stated as: (i) `G` is the distribution function of a probability measure on `ℝ`; (ii) for the
probability measure `ν` with distribution function `G` (unique), (2.60) = (2.61) for every
`z ∈ ℝ`, and the expected MSRT function of Definition 2.4 equals (2.61) `− γ`; (iii) for any data
`A, b, c, t` of (2.59), `(x, z)` solves (2.59) with the expected MSRT function iff it solves (2.59)
with the expected SRT function (2.61).

**Formalization Note.** `P` is the distribution of `ξ̃`, `hP` the existence of `𝔼_ξ̃[ξ̃]`
(the standing proviso for expected SRT functions, Definition 2.3, used for `μ` in the derivation
on p.241). `dF_ξ̃(ξ + u_k)` is integration against `P.map (· − u k)` and `dF_ξ̃(ξ − l_k)` against
`P.map (· + l k)` (their distribution functions are `F_ξ̃(· + u_k)`, `F_ξ̃(· − l_k)`, see
`eq_2_57_2_58`); `dG` is integration against any probability measure `ν` with `cdf ν = G`. The sums
`Σ_{k=k}^{K−1}` printed in (2.61) are read as `Σ_{k=0}^{K−1}`, as in (2.62)–(2.63) and in the
derivation on p.241 (`A = W_α`, `B = W_β`). The (2.60) expression omits the `−γ` of Definition 2.4;
both forms are stated. -/
theorem theorem_2_8 {K : ℕ} (α β u l : Fin K → ℝ) (hd : IsMSRTData K α β u l) (γ : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable (fun ξ => ξ) P) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(cdf ν) = mixtureCdf α β u l P) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ⇑(cdf ν) = mixtureCdf α β u l P →
      (∀ z : ℝ,
        ∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) +
            ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k)) =
          (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂ν -
            mixtureConst α β u l) ∧
      (∀ z : ℝ, expectedMSRT α β u l γ P z =
          (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂ν -
            mixtureConst α β u l - γ) ∧
      (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c t : Fin n → ℝ)
          (x : Fin n → ℝ) (z : ℝ),
        IsOptimal259 A b c t (expectedMSRT α β u l γ P) x z ↔
          IsOptimal259 A b c t
            (fun z' => (∑ k, α k) * ∫ ξ, (ξ - z')⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z')⁻ ∂ν -
              mixtureConst α β u l) x z) := by sorry

end KallMayerSLP.SimpleRecourse
