-- Prove2me | Theorems.Thm_OLPRegret_lemma_4
-- name    : OLPRegret.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:53.684843+00:00
-- url     : https://prove2.me/theorems/61588962-40a0-433a-803c-5ef292314c95
-- title:
--   Lemma 4 — the myopic regret under Algorithm 2 is $O(1/t)$ (corrected: for $t$ past a threshold)
-- statement:
--   Under Assumptions 2–6 and Algorithm 2, there is $\delta_0>0$ such that for every $\delta\in(0,\delta_0)$ there are $C>0$ and $T$ with
--   $$
--   \mathrm E^*\Big(\sup_{y}\ r_t\Big)\le C/t\qquad\text{for all }n\text{ and all }t\text{ with }T\le t\le n,
--   $$
--   where $r_t$ is the upper myopic regret and the supremum runs over all choices of shadow prices.
--
--   Differences from the source:
--   - correction: "for all $n\in\mathbb N$ and $t\le n$" → for all $n$ and $t$ with $T\le t\le n$; reason: false at small $t$ for every-minimizer shadow prices, and the proof works at "large $t$". Counterexample under all assumptions: $m=1$, $u\sim\mathrm{Uniform}[0,1]$, $a\equiv1$, $\beta=1/2$, $n=t=2$: on $u_2>1/2$, Algorithm 2 accepts, $\psi_2^{1/2}(1)=0$, every $y\ge u_1$ minimizes $\Lambda_1^0$, and $\Delta_2(y)^-=(y-u_2)^+$ is unbounded
--   - correction: the $r_t$ of (35) → the corrected $r_t$ of `OLPRegret.eq_35`; reason: same correction as (35); it changes $r_t$ only at $a_t\not\le tb_t$, which excludes large $t$ on $b_t\in B_{\delta/2}(\beta)$
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: expectation of a supremum over $b$ and minimizers → outer expectation (infimum of $\int Z$ over measurable majorants $Z$); reason: the supremum is not known to be measurable; the paper derives these bounds from van der Vaart and Wellner, whose convention this is, and it is the strong direction
--   - reading: $y_\infty^{b}$ in Algorithm 2, which Lemma 2 defines only near $\beta$ → any selection $y$ that minimizes $\Lambda_\infty^b$ for $b$ near $\beta$ and is arbitrary elsewhere; reason: the page does not define $y_\infty^b$ far from $\beta$; the bound holds for every such selection
--   - encoding: "sufficiently small" $\delta$, used on p.27 and in the proof → $\exists\delta_0\ \forall\delta\in(0,\delta_0)$; reason: the same claim with its order of quantifiers spelled out
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 4, p.28; proof Online Appendix pp.10–14

import Mathlib
import Definitions.Def_OLPRegret_algorithm2
import Definitions.Def_OLPRegret_myopicRegret
import Definitions.Def_PlugInRisk_outerExp

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 4, p.28 (corrected): the expected period-`t` myopic regret is
`O(1/t)` under Algorithm 2, with `C` free of `n` and `t`.

**Formalization Note** The supremum runs over all choices of shadow prices and the expectation is an
outer expectation. The bound starts at a threshold `T`: the printed "for all `n ∈ ℕ` and `t ≤ n`"
fails at small `t`, where `ψₜ^{bₜ}(aₜ)` can vanish; see the difference list. The proof on Online
Appendix pp.10–14 works at "large `t`". -/
theorem lemma_4 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) (y : E m → E m) (hy : IsLimitPrice μ β y) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ (n : ℕ) (t : Fin n), T ≤ period t →
        PlugInRisk.outerExp (sampleLaw μ n)
          (fun ω => ⨆ (Y : ℕ → E m → E m) (_ : IsShadowPriceChoice ω Y),
            ENNReal.ofReal (rUpper δ (algorithm2 y) β Y ω t)) ≤
          ENNReal.ofReal (C / (period t : ℕ)) := by sorry

end OLPRegret
