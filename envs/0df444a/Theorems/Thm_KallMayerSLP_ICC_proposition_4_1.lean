-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_proposition_4_1
-- name    : KallMayerSLP.ICC.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:42.332675+00:00
-- url     : https://prove2.me/theorems/a3f50e27-c0eb-4cf8-af37-3a3fa000ce8a
-- title:
--   Proposition 4.1 — integrated tails of $\mathbb E[(\vartheta-z)^+]$ and $\mathbb E[(\vartheta-z)^-]$
-- statement:
--   Let $\vartheta$ be a real random variable on a probability space whose expected value exists, with distribution function $F_\vartheta$, and let $z\in\mathbb R$. Write $u^+=\max\{0,u\}$ and $u^-=\max\{0,-u\}$. Then both $\mathbb E[(\vartheta-z)^+]$ and $\mathbb E[(\vartheta-z)^-]$ exist, and
--   $$
--   \mathbb E[(\vartheta-z)^+]=\int_z^\infty\big(1-F_\vartheta(t)\big)\,dt,\qquad
--   \mathbb E[(\vartheta-z)^-]=\int_{-\infty}^z F_\vartheta(t)\,dt.
--   $$
--   These formulas explain the word "integrated": an expected shortfall is an integral of tail probabilities.
--
--   **Formalization Note** "$\mathbb E[\vartheta]$ exists" is integrability of $\vartheta$. The statement also asserts that the two improper integrals exist, as Lebesgue integrals over $(z,\infty)$ and $(-\infty,z]$.
--
--   Differences from the source:
--
--   - encoding: 𝔼[ϑ] exists, i.e. ∫|t| dF_ϑ(t) is finite (p.147) → Integrable ϑ μ, with the existence of all four integrals as explicit clauses; reason: the Bochner integral would otherwise be 0; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.1 and (4.1), p.148 (PDF 158)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_distFn

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **Proposition 4.1 (integrated tails).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Proposition 4.1 and (4.1), p.148
(PDF 158). If `𝔼[ϑ]` exists, then for all `z ∈ ℝ` both `𝔼[(ϑ − z)⁺]` and `𝔼[(ϑ − z)⁻]` exist, and
`𝔼[(ϑ − z)⁺] = ∫_z^∞ (1 − F_ϑ(t)) dt`, `𝔼[(ϑ − z)⁻] = ∫_{−∞}^z F_ϑ(t) dt`.

**Formalization Note.** "`𝔼[ϑ]` exists" is the finiteness of `∫|t| dF_ϑ(t)` (p.147), i.e.
`Integrable ϑ μ`. Existence of both expectations and of both improper integrals is stated
explicitly, as a Bochner integral would otherwise be `0`. `u⁺ = max{0, u}`, `u⁻ = max{0, −u}`. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ϑ : Ω → ℝ) (hϑ : Integrable ϑ μ) (z : ℝ) :
    Integrable (fun ω => max 0 (ϑ ω - z)) μ ∧
    Integrable (fun ω => max 0 (-(ϑ ω - z))) μ ∧
    IntegrableOn (fun t => 1 - distFn μ ϑ t) (Set.Ioi z) ∧
    IntegrableOn (distFn μ ϑ) (Set.Iic z) ∧
    ∫ ω, max 0 (ϑ ω - z) ∂μ = ∫ t in Set.Ioi z, (1 - distFn μ ϑ t) ∧
    ∫ ω, max 0 (-(ϑ ω - z)) ∂μ = ∫ t in Set.Iic z, distFn μ ϑ t := by sorry

end KallMayerSLP.ICC
