-- Prove2me | Theorems.Thm_MetricMinTest_lemma_B_1
-- name    : MetricMinTest.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:25.404993+00:00
-- url     : https://prove2.me/theorems/04eb193d-1c5b-4d87-930f-32fe6f6eed29
-- title:
--   Lemma B.1, p.22 — screening statistics: Ville bound under the null, exponential drift on positive instances
-- statement:
--   Let $d$ be a pseudometric, $\gamma\in(0,1/4]$, and $P\in\mathcal P_d$. Let $r\in[0,\gamma)$, $z$ an index, and $w\ge0$ with $W=\sum_jw_j>0$ and $\sum_jw_j(\gamma-r-d(z,j))_+^2\ge1$. Put $p=w/W$ and $a_j=(\gamma-r-d(z,j))_+$. Let $I_1,I_2,\dots$ be independent draws from $p$, independent of the observations, let $X_s$ be a fresh observation from index $I_s$, and put
--   $$S_z(t)=\sum_{s=1}^t\Big[a_{I_s}\big(X_s-r-d(z,I_s)\big)-\tfrac12a_{I_s}^2\Big].$$
--   1. If $\mu_z<r$, then $\Pr(\sup_tS_z(t)\ge\beta)\le e^{-\beta}$ for every $\beta>0$.
--   2. If $\min_j\mu_j\ge\gamma$, then $\mathbb Ee^{-S_z(t)/2}\le e^{-t/(16W)}$ for every $t\ge0$.
--
--   One shared sample stream thus tests every target at once: soundness needs no union bound, and on positive instances every statistic drifts upward at rate $\Omega(1/W)$.
--
--   **Formalization Note** The index set carries the discrete measurable structure. The supremum over $t$ is taken in the extended reals.
--
--   Differences from the source:
--   - reading: the lemma's setting → $d$ a pseudometric, $\gamma\in(0,1/4]$, $P\in\mathcal P_d$; reason: the standing assumptions of §2 (p.6); part (i)'s proof uses $\mu_j\le\mu_z+d(z,j)$
--   - encoding: draws and fresh observations → draws $(I_s)\sim p^{\otimes\mathbb N}$ independent of the observation table, $X_s$ the next unread entry of stream $I_s$, the index type carrying measurable singletons; reason: stack-of-streams model; same joint law
--   - encoding: $\Pr(\sup_tS_z(t)\ge\beta)$ → probability of $\beta\le\sup_tS_z(t)$ with the supremum in the extended reals; reason: the supremum can be $+\infty$
--   - encoding: $\mathbb Ee^{-S_z(t)/2}$ → integral in $[0,\infty]$; reason: Lean convention; the integrand is nonnegative
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma B.1, p.22

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_InClass
import Definitions.Def_MetricMinTest_streamLaw
import Definitions.Def_MetricMinTest_drawLaw
import Definitions.Def_MetricMinTest_screenStat

namespace MetricMinTest

open MeasureTheory

/-- **Lemma B.1 (Screening statistics).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Lemma B.1, p.22: "Let
r ∈ [0, γ), z ∈ [k], and w ≥ 0 with W = ∑ⱼ wⱼ > 0 and ∑ⱼ wⱼ(γ − r − d(z, j))₊² ≥ 1. Put p = w/W
and aⱼ = (γ − r − d(z, j))₊. Let I₁, I₂, … be independent draws from p, independent of the
observations, let X_s be a fresh observation from index I_s, and put
S_z(t) = ∑_{s=1}^t [a_{I_s}(X_s − r − d(z, I_s)) − ½ a²_{I_s}]. (i) If µ_z < r, then
Pr(sup_t S_z(t) ≥ β) ≤ e^{−β} for every β > 0. (ii) If minⱼ µⱼ ≥ γ, then
E e^{−S_z(t)/2} ≤ e^{−t/(16W)} for every t ≥ 0."

**Formalization Note.** Standing setting (§2, p.6): `d` a pseudometric, `γ ∈ (0, 1/4]`, and the
instance in `P_d`. The experiment is `(I, ω) ∼ (w/W)^⊗ℕ ⊗ streamLaw P` on `(ℕ → ι) × (ι → ℕ → ℝ)`,
the draws independent of the observations (stack-of-streams encoding of "fresh observation"; the
index type carries a measurable structure with measurable singletons). `sup_t S_z(t)` is the
supremum in `EReal` over `t ∈ ℕ`. The expectation in (ii) is an `ℝ≥0∞` integral. -/
theorem lemma_B_1 {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (d : ι → ι → ℝ) (hd : IsPseudometric d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (P : Instance ι) (hP : InClass d P) (r : ℝ)
    (hr : r ∈ Set.Ico 0 γ) (z : ι) (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hW : 0 < ∑ j, w j)
    (hwz : 1 ≤ ∑ j, w j * (max (γ - r - d z j) 0) ^ 2) :
    (P.mean z < r → ∀ β : ℝ, 0 < β →
      ((Measure.infinitePi (fun _ : ℕ => drawLaw w)).prod (streamLaw P))
          {p | (β : EReal) ≤ ⨆ t : ℕ, ((screenStat d γ r z p.1 p.2 t : ℝ) : EReal)} ≤
        ENNReal.ofReal (Real.exp (-β))) ∧
    ((∀ j, γ ≤ P.mean j) → ∀ t : ℕ,
      ∫⁻ p, ENNReal.ofReal (Real.exp (-(screenStat d γ r z p.1 p.2 t) / 2))
          ∂((Measure.infinitePi (fun _ : ℕ => drawLaw w)).prod (streamLaw P)) ≤
        ENNReal.ofReal (Real.exp (-(t : ℝ) / (16 * ∑ j, w j)))) := by sorry

end MetricMinTest
