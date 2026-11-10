-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_lemma_4_3
-- name    : LemonsPoA.TwoSided.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:35.035617+00:00
-- url     : https://prove2.me/theorems/b11ad9ed-9969-48db-b41a-5be7f074cd49
-- title:
--   Lemma 4.3 — convex-order domination by an exponential gives $E[C\mathbf 1_A]\ge\frac\mu2\Pr[A]^2$
-- statement:
--   Let $C\ge 0$ be a random variable on a probability space with mean $\mu=E[C]\in(0,\infty)$, dominated in convex order by an exponential random variable $Z$ with mean $\mu$: $E[\varphi(C)]\le E[\varphi(Z)]$ for every convex $\varphi:\mathbb R\to\mathbb R$. Then every event $A$ satisfies
--   $$E[C\mathbf 1_A]\ \ge\ \frac\mu2\Pr[A]^2,$$
--   and consequently, if $\Pr[A]>0$, $E[C\mid A]\ge\frac\mu2\Pr[A]$.
--
--   Used with $A=\{\Sigma_S=\sigma^-_S\}$, it shows that a rare-enough pessimistic signal cannot drag the forecast of $C$ far below its mean.
--
--   **Formalization Note** $E[C\mid A]=E[C\mathbf 1_A]/\Pr[A]$; events are measurable sets; the convex order is stated on the law of $C$.
--
--   Differences from the source:
--   - encoding: for any convex $\varphi:\mathbb R\to\mathbb R$, $E[\varphi(C)]\le E[\varphi(Z)]$ → for every convex $\varphi$ with $\varphi(Z)$ integrable, $\varphi(C)$ is integrable and $E[\varphi(C)]\le E[\varphi(Z)]$ (Bochner integrals); reason: same condition: for convex $\varphi$ and integrable $C,Z$ both sides lie in $(-\infty,+\infty]$, and the inequality is trivial when $E[\varphi(Z)]=+\infty$; avoids the junk value 0 of a non-integrable integral
--   - encoding: $\mu=E[C]\in(0,\infty)$ → $C$ integrable and $0<\int C$; reason: the same condition for $C\ge 0$
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 22, Lemma 4.3

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- Lemma 4.3 (p. 22): if `C ≥ 0` is dominated in convex order by an exponential variable with
mean `µ = E[C] ∈ (0, ∞)`, then `E[C 1_A] ≥ (µ/2) Pr[A]²` for every event `A`, and
`E[C | A] ≥ (µ/2) Pr[A]` when `Pr[A] > 0`. -/
theorem lemma_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Ω → ℝ) (hCm : Measurable C) (hC0 : ∀ᵐ ω ∂P, 0 ≤ C ω) (hCi : Integrable C P)
    (μ : ℝ) (hμ : μ = ∫ ω, C ω ∂P) (hμpos : 0 < μ) (hcx : CxLeExp (P.map C) μ)
    (A : Set Ω) (hA : MeasurableSet A) :
    μ / 2 * (P A).toReal ^ 2 ≤ ∫ ω in A, C ω ∂P ∧
      (0 < (P A).toReal → μ / 2 * (P A).toReal ≤ (∫ ω in A, C ω ∂P) / (P A).toReal) := by sorry

end LemonsPoA.TwoSided
