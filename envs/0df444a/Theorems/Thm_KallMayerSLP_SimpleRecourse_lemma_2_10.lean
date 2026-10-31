-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_10
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:11.949157+00:00
-- url     : https://prove2.me/theorems/dbe1e3fb-dff5-4380-ab25-2bb2ee476a02
-- title:
--   Lemma 2.10 — SRT and expected SRT functions are convex
-- statement:
--   Let $\alpha,\beta,\gamma$ be real with $\alpha+\beta\ge0$, let $\varphi(z,\xi)=\alpha[\xi-z]^++\beta[\xi-z]^--\gamma$ be the SRT function, and let $\Phi(z)=\mathbb E_{\tilde\xi}[\varphi(z,\tilde\xi)]$ be the expected SRT function of a real random variable $\tilde\xi$ with finite mean. Then
--
--   1. $\xi\mapsto\varphi(z,\xi)$ is convex on $\mathbb R$ for every fixed $z$;
--   2. $z\mapsto\varphi(z,\xi)$ is convex on $\mathbb R$ for every fixed $\xi$;
--   3. $z\mapsto\Phi(z)$ is convex on $\mathbb R$.
--
--   Convexity of $\Phi$ is what makes the simple recourse problem a convex program, and convexity of $\varphi(z,\cdot)$ is what Jensen and Edmundson–Madansky bounds for $\Phi$ rest on.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.10, p.229 (PDF 238)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.10 (convexity of SRT and ESRT functions).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.10, p.229 (PDF 238),
with Definition 2.3, p.228 (PDF 237). Let `φ` be an SRT function (`α + β ≥ 0`) and `Φ` the
corresponding expected SRT function. Then `φ(z, ·)` is convex in `ξ` for any fixed `z ∈ ℝ`,
`φ(·, ξ)` is convex in `z` for any fixed `ξ ∈ ℝ`, and `Φ(·)` is convex in `z`.

**Formalization Note.** `P` is the distribution of `ξ̃`, a probability measure on `ℝ`; `hP` is the
book's standing proviso "`𝔼_ξ̃[ξ̃]` provided to exist" of Definition 2.3. -/
theorem lemma_2_10 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) :
    (∀ z : ℝ, ConvexOn ℝ Set.univ (fun ξ => srt α β γ z ξ)) ∧
    (∀ ξ : ℝ, ConvexOn ℝ Set.univ (fun z => srt α β γ z ξ)) ∧
    ConvexOn ℝ Set.univ (expectedSRT α β γ P) := by sorry

end KallMayerSLP.SimpleRecourse
