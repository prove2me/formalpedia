-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_claim_v
-- name    : NeuroMV.WellPosed.claim_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:02.393502+00:00
-- url     : https://prove2.me/theorems/f53592bb-ee65-4afa-b7af-35fe9a9cf174
-- title:
--   §2, claim (v), p. 10 — the Euler schemes converge to a solution of (6) (for 𝓡-a.e. r, p. 16)
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5). Fix $\omega'$ and $T>0$, and let $X^n$, $n\ge1$, be solutions on $[-\tau,T]$ of the Euler scheme (11)/(13) at $\omega'$. Then there is a process $X$ such that
--   1. for every $r\in\Gamma$ and every $\varepsilon > 0$,
--   $$\lim_{n\to\infty}\mathbb P\Big\{\sup_{t\in[0,T]}\big|X^{n,r}_t - X^r_t\big| > \varepsilon\Big\} = 0;$$
--   2. $X$ is a strong solution of equation (6) on $[-\tau,T]$, the integral identity of (6) holding for $\mathcal R$-almost every $r\in\Gamma$ (as the proof concludes on p. 16: "for $\mathcal R\times\mathbb P'$-almost all $(r,\omega')$"), while the initial condition, càdlàg paths, adaptedness and measurability in $(r,\omega)$ hold for every $r\in\Gamma$.
--
--   This is claim (v), the last step of the existence proof of Theorem 1.5.
--
--   **Formalization Note.** The statement is at a fixed $\omega'$, as is the proof. (H6) is omitted (network only).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, claim (v), p. 10 (proof pp. 15–16, conclusion p. 16)

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem claim_v
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (Xn : ℕ → Pos k → ℝ → Ω → SDEState d)
    (hX : ∀ ns : ℕ, 0 < ns → IsEulerScheme6 S C ν Nz τ ω' T ns (Xn ns)) :
    ∃ X : Pos k → ℝ → Ω → SDEState d,
      (∀ r ∈ S.Γ, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun ns : ℕ => Nz.prob {ω | ENNReal.ofReal ε <
            ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Xn ns r t ω - X r t ω‖ₑ}) atTop (𝓝 0)) ∧
      ∃ G : Set (Pos k), S.R (S.Γ \ G) = 0 ∧ SolvesOn S C ν Nz τ segMap ω' T G X := by sorry

end NeuroMV.WellPosed
