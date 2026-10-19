-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_lemma_3
-- name    : LimitedSwitching.HighProb.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:04.333184+00:00
-- url     : https://prove2.me/theorems/8c70e15f-bf0e-4177-a9c7-2ceded4c1af8
-- title:
--   Lemma 3, p. 10 (corrected: integral N, hypothesis at τ₀ only, boundary switches) — Framework 1 uses more than N epochs with probability ≤ e^{−N}
-- statement:
--   Let $\mathcal A$ be a randomized online algorithm for prediction from experts, with randomness $\omega\sim\mu$ on a probability space, whose actions depend measurably on $\omega$. Let $T\ge1$, let $N\ge2$ be an integer (playing the role of $\log(2/\delta)$, so that $\delta/2=e^{-N}$), and put $\tau_0=\min(T,\lceil 8T/N\rceil)$. Suppose there is $c_{\mathcal A}>0$ such that for every loss sequence with values in $[0,1]$
--   $$\mathbb E\big[\mathrm{Switches}_{\tau_0}(\mathcal A)\big]\le c_{\mathcal A}\sqrt{\tau_0}.$$
--   Let $\mathcal B$ be Framework 1 applied to $\mathcal A$ with budget $S'=23\,c_{\mathcal A}\sqrt{T/N}$, with independent randomness $\omega_0,\omega_1,\dots\sim\mu$ for the successive epochs. Then for every fixed loss sequence $(\ell_t)$ with values in $[0,1]$, the number $E$ of epochs used in rounds $1,\dots,T$ satisfies
--
--   $$\mathbb P(E>N)\le e^{-N}\qquad\text{and}\qquad \mathbb P\big(\mathrm{Switches}_T(\mathcal B)>N(S'+1)\big)\le e^{-N}.$$
--
--   This is the paper's black-box high-probability switching bound. Theorem 8 uses it both for the switching guarantee and to control the number of epochs in the regret bound.
--
--   **Formalization Note** Three corrections to the printed lemma, all disclosed. (1) Integrality: $N$ is a natural number $\ge2$ and $\delta/2$ is written $e^{-N}$. (2) The hypothesis is required only at the single horizon $\tau_0$ that the proof uses (L$_{\rm target}=8T/N$, or $T$ when $8T/N>T$). This is implied by the printed "for all $\tau\le T$", so the formal lemma is at least as strong as the printed one. It is also the form that FPL$^*$ satisfies in Theorem 8. (3) The second bound is $N(S'+1)$ rather than $N S'$, because each new epoch may begin on a different action, adding one switch per boundary. Measurability of $\mathcal A$ in $\omega$ is assumed: without it a lower integral of the switch count can vanish while the switches are large on a non-measurable set of outer measure one. Probabilities are outer measures of the bad events.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 10, Lemma 3; proof pp. 10–12 (Lemma 4 and footnote 4, p. 11)

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (A : OnlineAlg Ω n) (hA_meas : ∀ t past, Measurable (fun ω => A ω t past))
    (T N : ℕ) (hT : 1 ≤ T) (hN : 2 ≤ N) (cA : ℝ) (hcA : 0 < cA)
    (hA : ∀ ℓ : ℕ → Fin n → ℝ, IsLossSeq ℓ →
      ∫⁻ ω, (switches (min T ⌈8 * (T : ℝ) / N⌉₊) (play A ω ℓ) : ℝ≥0∞) ∂μ
        ≤ ENNReal.ofReal (cA * √(min T ⌈8 * (T : ℝ) / N⌉₊ : ℕ)))
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) :
    (Measure.infinitePi (fun _ : ℕ => μ))
        {ω | N < numEpochs A (23 * cA * √((T : ℝ) / N)) ω ℓ T}
        ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) ∧
      (Measure.infinitePi (fun _ : ℕ => μ))
        {ω | (N : ℝ) * (23 * cA * √((T : ℝ) / N) + 1)
          < switches T (play (batch A (23 * cA * √((T : ℝ) / N))) ω ℓ)}
        ≤ ENNReal.ofReal (Real.exp (-(N : ℝ))) := by sorry

end LimitedSwitching.HighProb
