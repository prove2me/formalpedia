-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_11
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:12.305407+00:00
-- url     : https://prove2.me/theorems/a6ac9785-48e9-4aec-bc57-85688ecfc1bd
-- title:
--   Lemma 2.11 — asymptotes of the expected SRT function and exactness outside the support
-- statement:
--   Let $\alpha+\beta\ge0$, let $\tilde\xi$ have law $\mathbb P_{\tilde\xi}$, distribution function $F_{\tilde\xi}$ and finite mean $\mu=\mathbb E_{\tilde\xi}[\tilde\xi]$, and let $\Phi$ be the expected SRT function. Then
--
--   $$
--   \Phi(z)=\mathbb E_{\tilde\xi}[\varphi(z,\tilde\xi)]=\int(\alpha[\xi-z]^++\beta[\xi-z]^-)\,dF_{\tilde\xi}(\xi)-\gamma=\Bigl\{\alpha\int_z^\infty[\xi-z]\,dF_{\tilde\xi}(\xi)+\beta\int_{-\infty}^z[z-\xi]\,dF_{\tilde\xi}(\xi)\Bigr\}-\gamma ,
--   $$
--
--   and
--
--   1. $\Phi(z)-\varphi(z,\mu)\to0$ and $\Phi(z)-[\alpha(\mu-z)-\gamma]\to0$ as $z\to-\infty$;
--   2. $\Phi(z)-\varphi(z,\mu)\to0$ and $\Phi(z)-[\beta(z-\mu)-\gamma]\to0$ as $z\to+\infty$;
--   3. if $\mathbb P_{\tilde\xi}(\xi<a)=0$, then $\Phi(z)=\alpha(\mu-z)-\gamma=\varphi(z,\mu)$ for all $z\le a$;
--   4. if $\mathbb P_{\tilde\xi}(\xi>b)=0$, then $\Phi(z)=\beta(z-\mu)-\gamma=\varphi(z,\mu)$ for all $z\ge b$.
--
--   So $\Phi$ has the two branches of $\varphi(\cdot,\mu)$ as asymptotes and coincides with them outside the convex hull of the support.
--
--   **Formalization Note** $\int_z^\infty$ is the integral over $(z,\infty)$ and $\int_{-\infty}^z$ over $(-\infty,z]$; the integrands vanish at $\xi=z$.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
--   - encoding: ∫_z^∞ … dF_ξ̃ and ∫_{−∞}^z … dF_ξ̃ → set integrals over Set.Ioi z and Set.Iic z; reason: the integrands vanish at ξ = z, so the endpoint convention changes nothing
--   - generalization: If ℙ(ξ < a) = 0 and ℙ(ξ > b) = 0 then Φ(z) = α(μ − z) − γ = φ(z, μ) for z ≤ a and Φ(z) = β(z − μ) − γ = φ(z, μ) for z ≥ b → each clause under its own hypothesis: ℙ(ξ < a) = 0 gives the z ≤ a clause, ℙ(ξ > b) = 0 the z ≥ b clause; reason: when both hypotheses hold this is the printed statement; the text after the lemma (a := inf supp > −∞ ⟹ …, b := sup supp < ∞ ⟹ …) uses the clauses separately
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.11, p.230 (PDF 239)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory Filter Topology

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.11 (asymptotes of the ESRT function; exactness outside the support).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.11, p.230 (PDF 239).
For `Φ(z) := 𝔼_ξ̃[φ(z, ξ̃)] = ∫ (α[ξ − z]⁺ + β[ξ − z]⁻) dF_ξ̃(ξ) − γ
= {α ∫_z^∞ [ξ − z] dF_ξ̃(ξ) + β ∫_{−∞}^z [z − ξ] dF_ξ̃(ξ)} − γ` holds, with `μ = 𝔼_ξ̃[ξ̃]`:
`Φ(z) − φ(z, μ) = Φ(z) − [α(μ − z) − γ] → 0` as `z → −∞`, and
`Φ(z) − φ(z, μ) = Φ(z) − [β(z − μ) − γ] → 0` as `z → +∞`.
In particular, if `ℙ_ξ̃(ξ < a) = 0` then `Φ(z) = α(μ − z) − γ = φ(z, μ)` for `z ≤ a`, and if
`ℙ_ξ̃(ξ > b) = 0` then `Φ(z) = β(z − μ) − γ = φ(z, μ)` for `z ≥ b`.

**Formalization Note.** `P` is the distribution of `ξ̃` (probability measure on `ℝ`), `hP` the
existence of `μ`. `∫_z^∞` is the integral over `(z, ∞)` and `∫_{−∞}^z` over `(−∞, z]`; the
integrands vanish at `ξ = z`, so the endpoint convention is immaterial. The two "in particular"
clauses are stated separately (each needs only its own hypothesis); together they give the
printed joint statement. -/
theorem lemma_2_11 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) :
    (∀ z : ℝ, expectedSRT α β γ P z = ∫ ξ, srt α β γ z ξ ∂P ∧
      expectedSRT α β γ P z =
        (α * ∫ ξ in Set.Ioi z, (ξ - z) ∂P + β * ∫ ξ in Set.Iic z, (z - ξ) ∂P) - γ) ∧
    Tendsto (fun z => expectedSRT α β γ P z - srt α β γ z (∫ ξ, ξ ∂P)) atBot (𝓝 0) ∧
    Tendsto (fun z => expectedSRT α β γ P z - (α * ((∫ ξ, ξ ∂P) - z) - γ)) atBot (𝓝 0) ∧
    Tendsto (fun z => expectedSRT α β γ P z - srt α β γ z (∫ ξ, ξ ∂P)) atTop (𝓝 0) ∧
    Tendsto (fun z => expectedSRT α β γ P z - (β * (z - ∫ ξ, ξ ∂P) - γ)) atTop (𝓝 0) ∧
    (∀ a : ℝ, P (Set.Iio a) = 0 → ∀ z ≤ a,
      expectedSRT α β γ P z = α * ((∫ ξ, ξ ∂P) - z) - γ ∧
        α * ((∫ ξ, ξ ∂P) - z) - γ = srt α β γ z (∫ ξ, ξ ∂P)) ∧
    (∀ b : ℝ, P (Set.Ioi b) = 0 → ∀ z, b ≤ z →
      expectedSRT α β γ P z = β * (z - ∫ ξ, ξ ∂P) - γ ∧
        β * (z - ∫ ξ, ξ ∂P) - γ = srt α β γ z (∫ ξ, ξ ∂P)) := by sorry

end KallMayerSLP.SimpleRecourse
