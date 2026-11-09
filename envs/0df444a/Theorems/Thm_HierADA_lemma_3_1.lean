-- Prove2me | Theorems.Thm_HierADA_lemma_3_1
-- name    : HierADA.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:00.136633+00:00
-- url     : https://prove2.me/theorems/808dbad4-e0af-43d9-adf1-3d533ac3babc
-- title:
--   Lemma 3.1 — existence of accurate reference weights (corrected: explicit sample size)
-- statement:
--   Let $\varepsilon\in[0,1]$ and $\alpha,\xi,\delta\in(0,1)$ with $\delta\le\frac{\alpha\xi}{32}$, and let $r\ge\frac{1024}{\alpha^2}\ln\frac{4(k+1)}{\xi}$. Let $S=(X_1,\dots,X_r)\sim D^r$ on a finite domain $U$, and let $T=M(S)$ be the finite-valued transcript of an $(\varepsilon,\delta)$-differentially private mechanism interacting with a fixed analyst. Let $f_1(T,\cdot),\dots,f_k(T,\cdot):U\to[0,1]$ be queries that may depend on the transcript. Then, with probability at least $1-\xi$ over $(S,T)$, there is a single vector $u\in\mathbb R^r$ with
--
--   $$
--   u_i\ge0,\qquad\sum_iu_i=1,\qquad u_i\le\frac8r,\qquad R(u)=\frac r2\sum_i\Big(u_i-\frac1r\Big)^2\le\varepsilon^2,
--   $$
--
--   and, for every $t\le k$,
--
--   $$
--   \Big|\sum_iu_if_t(T,X_i)-Df_t(T,\cdot)\Big|\le\alpha .
--   $$
--
--   Even though the transcript can bias the empirical averages, a privacy budget $\varepsilon\le1$ leaves a near-uniform reweighting of the sample that answers all of the transcript's queries accurately. Proposition 3.2 applies this lemma to every block of the hierarchical mechanism.
--
--   **Formalization Note** $(\varepsilon,\delta)$-privacy is the published `ContinualCounting.IsApproxDP` for the neighbour relation `PrivLearn.Generic.Neighbors`, and $W$ is the published `NondualOpt.cappedSimplex r 8`. The mechanism together with the fixed analyst is given by its transcript law $S\mapsto M(S)$, a probability mass function on a finite type with the discrete σ-algebra. The probability is that of the joint law of $(S,T)$, applied to the complement of the good set.
--
--   Differences from the source:
--   - correction: “there exists sample complexity r = O((1/α²) log(k/ξ))” → every r with (1024/α²) ln(4(k+1)/ξ) ≤ r; reason: as printed it fails: for k = 1 and ξ = exp(−α²/(2C)) the O-form allows only r = 0, where no u has Σ u_i = 1; the threshold is the proof's (p.15) and the one Proposition 3.2 and Theorem 3.7 use (p.25)
--   - encoding: T = M(S), the completed transcript of an (ε, δ)-private mechanism interacting with a fixed analyst → a map M from datasets to a PMF on a finite discrete type, (ε, δ)-DP for neighbouring datasets; reason: a mechanism with a fixed analyst is exactly such a map, and its transcript is finite-valued by assumption
--   - encoding: with probability at least 1 − ξ there exists u → the joint law of (S, T) gives the set where no such u exists probability at most ξ; reason: complementary events on a finite space
--   - encoding: t ≤ k (1-based) → t : Fin k; reason: renumbering only
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Lemma 3.1, p.14 (statement continued on p.15), sample size from the proof, p.15

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_penalty

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Lemma 3.1 (Existence of accurate reference weights)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Lemma 3.1, pp.14–15, with the sample size of its proof (p.15).

Let `ε ∈ [0, 1]`, `α, ξ, δ ∈ (0, 1)` with `δ ≤ αξ/32`, and `r ≥ (1024/α²) ln(4(k+1)/ξ)`. Let
`S ∼ D^r` on a finite domain `U`, and let `T = M(S)` be the finite-valued transcript of an
`(ε, δ)`-private mechanism interacting with a fixed analyst, given by its law `M S`. For queries
`f_1(T, ·), …, f_k(T, ·) : U → [0, 1]`, with probability at least `1 − ξ` over `(S, T)` there is a
single `u ∈ W` (`u_i ≥ 0`, `∑ u_i = 1`, `u_i ≤ 8/r`) with `R(u) ≤ ε²` and
`|∑_i u_i f_t(T, X_i) − D f_t(T, ·)| ≤ α` for every `t ≤ k`.

**Formalization Note.** The mechanism together with the fixed analyst is its transcript map
`M : (Fin r → U) → PMF 𝒯` with `𝒯` finite and discrete. The joint law of `(S, T)` is
`S ∼ iid D r` followed by `T ∼ M S`; the bound is on the probability of the complement of the good
set. **Correction:** the printed "there exists sample complexity `r = O((1/α²) log(k/ξ))`" is
replaced by "every `r ≥ (1024/α²) ln(4(k+1)/ξ)`", the threshold of the proof (p.15): for `k = 1` and
`ξ = e^{−α²/(2C)}`, the O-form allows only `r = 0`, where no `u` sums to one. -/
theorem lemma_3_1 {U 𝒯 : Type} [Fintype U] [Fintype 𝒯] [MeasurableSpace 𝒯]
    [MeasurableSingletonClass 𝒯] (D : PMF U) (r k : ℕ) (ε α ξ δ : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδ : δ ≤ α * ξ / 32)
    (hr : 1024 / α ^ 2 * Real.log (4 * ((k : ℝ) + 1) / ξ) ≤ r)
    (M : (Fin r → U) → PMF 𝒯) (hM : ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors (fun s => (M s).toMeasure) ε δ)
    (f : Fin k → 𝒯 → StatisticalQuery U) :
    ((iid D r).bind fun s => (M s).map fun T => (s, T)).toOuterMeasure
      {x | ¬ ∃ u ∈ NondualOpt.cappedSimplex r 8, penalty r u ≤ ε ^ 2 ∧
          ∀ t : Fin k, |∑ i, u i * (f t x.2 (x.1 i) : ℝ) - populationMean D (f t x.2)| ≤ α}
      ≤ ENNReal.ofReal ξ := by sorry

end HierADA
