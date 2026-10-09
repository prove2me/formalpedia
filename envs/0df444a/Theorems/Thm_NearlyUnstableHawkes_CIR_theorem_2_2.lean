-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_theorem_2_2
-- name    : NearlyUnstableHawkes.CIR.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:01.198979+00:00
-- url     : https://prove2.me/theorems/fc2cfd13-0bfd-4fc2-b7f0-7618b9a7dd85
-- title:
--   Theorem 2.2 — CIR limit of the renormalized Hawkes intensity and count
-- statement:
--   Let $N^T$ be a Hawkes process with baseline rate $\mu>0$ and excitation kernel $\phi^T=a_T\phi$. Assume that $\phi$ satisfies Assumption 1, that the rescaled resolvent densities $\rho^T$ are uniformly bounded as in Assumption 2, and that $T(1-a_T)\to\lambda>0$. Define $C^T_t=(1-a_T)\lambda^T_{tT}$ and $V^T_t=(1-a_T)N^T_{tT}/T$ for $0\le t\le1$. The rescaled intensity converges in law in the Skorohod topology on $D[0,1]$ to the law of the unique strong solution, started at zero, of
--
--   $$X_t=\int_0^t(\mu-X_s)\frac{\lambda}{m}\,ds+\frac{\sqrt\lambda}{m}\int_0^t\sqrt{X_s}\,dB_s.$$
--
--   Separately, $V^T$ converges in law in the same topology to $t\mapsto\int_0^t X_s\,ds$. This identifies the stochastic intensity limit and the associated accumulated-count limit.
--
--   **Formalization Note** $T$ runs along a sequence, and the Hawkes processes may live on different probability spaces. The statement asserts existence of a strong CIR solution and convergence to every such solution; these two clauses pin down the limit law. The SDE substrate defines a global solution, which is restricted here to $[0,1]$. Skorohod convergence uses a coupling with time changes. `Real.sqrt` is evaluated only on the solution's nonnegative values.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 10, Theorem 2.2; pp. 5, 7–9, Assumptions 1–2 and (1)–(3)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting
import Definitions.Def_EthierKurtz_SolvesBrownianSDE

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace NearlyUnstableHawkes.CIR

/-- Theorem 2.2, p. 10: the rescaled intensity and count converge to CIR and its integral. -/
theorem theorem_2_2 {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ) (m lam μ : ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hμ : 0 < μ) (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) (hρ : Assumption2 T a φ)
    (hN : ∀ n, IsHawkes (P n) μ (fun s => a n * φ s) (T n) (N n)) :
    (∃ (Ω' : Type) (m' : MeasurableSpace Ω'),
      letI := m'
      ∃ P' : Measure Ω', IsProbabilityMeasure P' ∧
        ∃ (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 1),
          EthierKurtz.IsStandardBrownian P' B ∧
          EthierKurtz.SolvesBrownianSDE P' (cirDiff lam m)
            (cirDrift μ lam m) B (fun _ => 0) X) ∧
    (∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 1),
      IsProbabilityMeasure P' →
      EthierKurtz.IsStandardBrownian P' B →
      EthierKurtz.SolvesBrownianSDE P' (cirDiff lam m)
        (cirDrift μ lam m) B (fun _ => 0) X →
      ConvInLawSkorohod01 P (C T a μ φ N) P'
        (fun t ω => X t.toNNReal ω 0) ∧
      ConvInLawSkorohod01 P (V T a N) P'
        (fun t ω => ∫ s in (0 : ℝ)..t, X s.toNNReal ω 0)) := by sorry

end NearlyUnstableHawkes.CIR
