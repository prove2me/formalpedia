-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_scheme_exists
-- name    : NeuroMV.WellPosed.scheme_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:56.435003+00:00
-- url     : https://prove2.me/theorems/b4d297d4-8c9b-4eae-94a7-f37bfe2f6051
-- title:
--   §2, proof of Theorem 1.5, p. 9 — the Euler scheme (11) exists and is measurable in (t, r, ω, ω′)
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5), and fix $T > 0$ and a step number $n \ge 1$. Then there is a process $X^{n,r}_t(\omega,\omega')$ that is jointly measurable in $(t,r,\omega,\omega')\in[-\tau,T]\times\Gamma\times\Omega\times\Omega'$ and is, for every $\omega'\in\Omega'$, a solution on $[-\tau,T]$ of the semi-implicit Euler scheme (11), equivalently of its integral form (13):
--
--   $$X^{n,r}_t = X^{n,r}_{k\tau/n} + \int_{k\tau/n}^t f(s,r,X^{n,r}_{s-},\omega')ds + \cdots + \sum_{\alpha=1}^P\int_{k\tau/n}^t\!\!\int_U\tilde{\mathbb E}\int_{\Gamma_\alpha}\eta\big(s,r,r',X^{n,r}_{s-},Y^{n,r'}_{\kappa(n,(s-\tau):s)},\omega',\xi\big)\mathcal R(dr')\tilde N^\alpha(ds,d\xi),\quad t\in\Big]\frac{k\tau}{n},\frac{(k+1)\tau}{n}\Big],$$
--
--   with $X^{n,r}_t = \hat z^\zeta_t$ on $[-\tau,0]$ for $r\in\Gamma_\zeta$. The paper obtains each step from Theorem A.2. This is the first step of the existence proof of Theorem 1.5.
--
--   **Formalization Note.** (H6) of Hypothesis 1.1 is omitted: it concerns the network (1) only and is not used.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, (11) and the sentence following it, p. 9

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem scheme_exists
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (T : ℝ) (hT : 0 < T) (ns : ℕ) (hns : 0 < ns) :
    ∃ Xn : Ω' → Pos k → ℝ → Ω → SDEState d,
      Measurable (fun p : Set.Icc (-τ) T × Pos k × Ω × Ω' => Xn p.2.2.2 p.2.1 p.1 p.2.2.1) ∧
      ∀ ω' : Ω', IsEulerScheme6 S C ν Nz τ ω' T ns (Xn ω') := by sorry

end NeuroMV.WellPosed
