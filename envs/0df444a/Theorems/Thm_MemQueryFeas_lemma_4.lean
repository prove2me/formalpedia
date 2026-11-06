-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_4
-- name    : MemQueryFeas.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:38:40.20967+00:00
-- url     : https://prove2.me/theorems/96c6585f-b0b1-4927-ae63-41b0bd551104
-- title:
--   Lemma 4 — $1\le\lambda_{\min}(T_v)\le\lambda_{\max}(T_v)\le 2/(d\delta_p^{(0)})$ with probability $1-2Pe^{-d/288}$
-- statement:
--   Let $P\ge2$, let $\tilde d$ satisfy $36P\tilde d\le d$, let $0<\varepsilon\le e^{-d}$, and let $E_1,\dots,E_P$ be independent with law $\mathrm{Unif}(\mathrm{Gr}(\tilde d,d))$. With probability at least $1-2Pe^{-d/288}$ over $E_1,\dots,E_P$, the following holds simultaneously for every admissible outcome of the NoiseAddition steps of Algorithm 2 (every choice of $\tilde d$-dimensional versions, each within largest principal angle $\delta_p^{(i)}/\sqrt{3P}$ of its predecessor), every $p\in[P]$ and every $v\in V_{p-1}$:
--   $$
--   1\le\lambda_{\min}(T_v)\le\lambda_{\max}(T_v)\le\frac{2}{d\,\delta_p^{(0)}} .
--   $$
--
--   The condition number of $T_v$ is thus controlled by its last stretching factor only, not by the product of all of them; this bound enters the validity of the hard instance (Lemma 1) and the reduction to the compression game (Proposition 2).
--
--   Differences from the source:
--   - encoding: "regardless of the randomness used in NoiseAddition" → for every admissible outcome of the NoiseAddition steps (IsAdmissibleNoise), inside the event over E_1,…,E_P; reason: App. D.1, p.37: the result holds simultaneously for all admissible noisy versions; this is the literal content of the phrase
--   - encoding: λ_min, λ_max (singular values) → inf_{‖x‖=1} ‖T x‖ and the operator norm ‖T‖; reason: the same quantities
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 4, p.15 (PDF p.16); App. D.1, p.37

import Mathlib
import Definitions.Def_MemQueryFeas_IsHaarGr
import Definitions.Def_MemQueryFeas_IsAdmissibleNoise
import Definitions.Def_MemQueryFeas_Tmap
import Definitions.Def_DissolveCDF_sigmaMin

open MeasureTheory ProbabilityTheory

namespace MemQueryFeas

/-- **Lemma 4 (condition number bound on transformations).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 4, p.15 (PDF p.16): "Let
`P ≥ 2` and `36P d̃ ≤ d`. With at least `1 − 2Pe^{−d/288}` probability over `E_1, ..., E_P`,
simultaneously over all `p ∈ [P]` and `v ∈ V_{p−1}`, we have `1 ≤ λ_min(T_v) ≤ λ_max(T_v) ≤ 2/(dδ_p^(0))`
regardless of the randomness used in NoiseAddition for sampling phases in each layer."

For i.i.d. Haar `E_1, …, E_P ∈ Gr(d̃, d)`, with probability at least `1 − 2Pe^{−d/288}` the following
holds for **every** admissible outcome `c` of the NoiseAddition steps (`IsAdmissibleNoise`), every
`p ∈ [P]` and every `v ∈ V_{p−1}`: `1 ≤ λ_min(T_v) ≤ λ_max(T_v) ≤ 2/(dδ_p^(0))`.

**Formalization Note.** `λ_min = DissolveCDF.sigmaMin` (infimum of `‖T x‖` over the unit sphere),
`λ_max = ‖·‖` (operator norm); `T_v = Tmap`. `d̃` is any
dimension with `36P d̃ ≤ d`, as stated. `0 < ε ≤ e^{−d}` is the standing assumption of §3 (the
accuracies `δ_p^(i)` and `N_p` are those of p.7). -/
theorem lemma_4 (d P dt : ℕ) (hP : 2 ≤ P) (hdt : 36 * P * dt ≤ d) (ε : ℝ) (hε : 0 < ε)
    (hεd : ε ≤ Real.exp (-(d : ℝ))) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ν : Measure (Op d)) (hν : IsHaarGr dt ν) (Eb : ℕ → Ω → Op d)
    (hEb : ∀ p, Measurable (Eb p)) (hind : iIndepFun (fun p : Fin P => Eb (p.1 + 1)) μ)
    (hlaw : ∀ p, 1 ≤ p → p ≤ P → μ.map (Eb p) = ν) :
    ENNReal.ofReal (1 - 2 * P * Real.exp (-(d : ℝ) / 288)) ≤
      μ {ω | ∀ c : ℕ → List ℕ → ℕ → Op d, IsAdmissibleNoise d ε P dt (fun p => Eb p ω) c →
        ∀ p, 1 ≤ p → p ≤ P → ∀ v, IsPhase (Np d ε P) (p - 1) v →
          1 ≤ DissolveCDF.sigmaMin (Tmap (delta d ε P) c v) ∧
          DissolveCDF.sigmaMin (Tmap (delta d ε P) c v) ≤ ‖Tmap (delta d ε P) c v‖ ∧
          ‖Tmap (delta d ε P) c v‖ ≤ 2 / (d * delta d ε P p 0)} := by sorry

end MemQueryFeas
