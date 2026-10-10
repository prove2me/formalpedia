-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_claim_iv
-- name    : NeuroMV.WellPosed.claim_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:52.48965+00:00
-- url     : https://prove2.me/theorems/2a504d0e-59ef-4b0b-bc50-09ac02405ecd
-- title:
--   §2, claim (iv), p. 10 — the Euler schemes are Cauchy in probability, uniformly on [0, T]
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5). Fix $\omega'$ and $T>0$, and let $X^n$, $n \ge 1$, be solutions on $[-\tau,T]$ of the Euler scheme (11)/(13) at $\omega'$ with step $\tau/n$. Then for every $r\in\Gamma$ and every $\varepsilon>0$,
--
--   $$\lim_{n,m\to\infty}\mathbb P\Big\{\sup_{t\in[0,T]}\big|X^{n,r}_t - X^{m,r}_t\big| > \varepsilon\Big\} = 0.$$
--
--   This is claim (iv) of the existence proof of Theorem 1.5: it yields the limit process of claim (v).
--
--   **Formalization Note.** The double limit is along the product filter $\text{atTop}\times\text{atTop}$ on $\mathbb N\times\mathbb N$; the supremum is in $[0,\infty]$; the value of the sequence at $n = 0$ is irrelevant. The statement is at a fixed $\omega'$, as the proof is. (H6) is omitted.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, claim (iv), p. 10 (proof pp. 13–14)

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem claim_iv
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (Xn : ℕ → Pos k → ℝ → Ω → SDEState d)
    (hX : ∀ ns : ℕ, 0 < ns → IsEulerScheme6 S C ν Nz τ ω' T ns (Xn ns)) :
    ∀ r ∈ S.Γ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun q : ℕ × ℕ => Nz.prob {ω | ENNReal.ofReal ε <
          ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Xn q.1 r t ω - Xn q.2 r t ω‖ₑ})
        (atTop ×ˢ atTop) (𝓝 0) := by sorry

end NeuroMV.WellPosed
