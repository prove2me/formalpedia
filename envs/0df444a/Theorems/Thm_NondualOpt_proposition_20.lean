-- Prove2me | Theorems.Thm_NondualOpt_proposition_20
-- name    : NondualOpt.proposition_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:56.686076+00:00
-- url     : https://prove2.me/theorems/fafb0107-6670-4aec-bc74-d8d73d0b0350
-- title:
--   Proposition 20 — sequential one-sided offset bound
-- statement:
--   Let $Z$ be a measurable space and $C$ a nonempty class of measurable functions $Z\to[0,2]$ that is pointwise measurable: some countable $C_0\subseteq C$ has every $h\in C$ as a pointwise limit of a sequence in $C_0$. Let $T\ge1$ and let $X_1,\dots,X_T$ be generated adaptively, $X_t\sim P_t(\cdot\mid X_{1:t-1})$. Then for every $0<\delta\le1$,
--   $$
--   \mathbb E\sup_{h\in C}\Big[\frac1T\sum_{t=1}^TP_th-\frac2T\sum_{t=1}^Th(X_t)\Big]\le4\delta+\frac{16}T+\frac{48}T\int_\delta^1\log N^{\mathrm{seq}}_\infty\big(\alpha/4,C,2T\big)\,d\alpha .
--   $$
--   Here $P_th=\int h\,dP_t(\cdot\mid X_{1:t-1})$. Sequential symmetrization and chaining turn the offset process into an entropy integral; with Lemma 5 and Lemma 22 it gives the upper bound of Theorem 6.
--
--   Differences from the source:
--   - encoding: an adaptive strategy of kernels P_t(· | X_{1:t−1}) → a measurable process on a probability space whose conditional law given X_{<t} is a Markov kernel κ_t evaluated at the past (conditional expectations of indicators); rounds 0-based; reason: every adaptive strategy is realized this way
--   - encoding: E sup_h and ∫_δ^1 log N dα → Bochner expectation of a real supremum over C as a type (bounded in [−4, 2], measurable by pointwise measurability), compared via ofReal with a lower Lebesgue integral in [0, ∞]; reason: no junk value: the entropy integrand may be infinite
--   - encoding: T rounds → T ≥ 1; reason: the bound divides by T
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 20, p.28 (pointwise measurability: preamble, p.28)

import Mathlib
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_NondualOpt_seqCoverNum
import Definitions.Def_NondualOpt_logN

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace NondualOpt

/-- **Proposition 20 (Sequential one-sided offset bound).** Let `Z` be any measurable space and `C`
a nonempty pointwise-measurable class of measurable functions `Z → [0, 2]`. For every adaptive
strategy of kernels `P_t(· | X_{1:t−1})` on `Z` and every `0 < δ ≤ 1`,
`E sup_{h ∈ C} [(1/T)∑_t P_t h − (2/T)∑_t h(X_t)] ≤ 4δ + 16/T + (48/T) ∫_δ^1 log N^seq_∞(α/4, C, 2T) dα`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 20, p.28, with the pointwise
measurability of the preamble on p.28.

**Formalization Note.** (i) The adaptive process is a measurable process `X_0, …, X_{T−1}` on a
probability space whose conditional law given the past `X_{<t}` is the Markov kernel `κ t`
evaluated at the past (conditional expectations of indicators); every adaptive strategy is
realized this way. Rounds are 0-based. (ii) The supremum over `C` is a real `⨆` over the
subtype; the family lies in `[−4, 2]` and, by pointwise measurability, is a countable supremum,
so the expectation is a genuine integral. (iii) The entropy integral is a lower Lebesgue integral
in `ℝ≥0∞` of `logN`, and the left side is compared through `ENNReal.ofReal` (a negative
expectation satisfies the bound trivially). `T ≥ 1`. -/
theorem proposition_20 {Z : Type*} [MeasurableSpace Z] (C : Set (Z → ℝ)) (hCne : C.Nonempty)
    (hCmeas : ∀ h ∈ C, Measurable h) (hCrange : ∀ h ∈ C, ∀ z, 0 ≤ h z ∧ h z ≤ 2)
    (hCpw : ∃ C₀ ⊆ C, C₀.Countable ∧ ∀ h ∈ C, ∃ hs : ℕ → Z → ℝ, (∀ k, hs k ∈ C₀) ∧
      ∀ z, Tendsto (fun k => hs k z) atTop (𝓝 (h z)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (hT : 1 ≤ T) (Xp : Fin T → Ω → Z) (hX : ∀ t, Measurable (Xp t))
    (κ : (t : Fin T) → Kernel (Fin t → Z) Z) [∀ t, IsMarkovKernel (κ t)]
    (hlaw : ∀ t : Fin T, ∀ s : Set Z, MeasurableSet s →
      P[(Xp t ⁻¹' s).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (fun ω => histPrefix (fun i => Xp i ω) t) MeasurableSpace.pi]
        =ᵐ[P] fun ω => (κ t (histPrefix (fun i => Xp i ω) t) s).toReal)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (∫ ω, ⨆ h : C, ((1 / T : ℝ) * ∑ t,
          ∫ z, (h : Z → ℝ) z ∂(κ t (histPrefix (fun i => Xp i ω) t)) -
        (2 / T : ℝ) * ∑ t, (h : Z → ℝ) (Xp t ω)) ∂P) ≤
      ENNReal.ofReal (4 * δ + 16 / T) +
        ENNReal.ofReal (48 / T) * ∫⁻ α in Set.Ioc δ 1, logN (seqCoverNum C (α / 4) (2 * T)) := by sorry

end NondualOpt
