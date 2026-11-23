-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_adaptive_poisson_data_processing
-- name    : LindbladTolerant.Testing.adaptive_poisson_data_processing
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:02:54.8664+00:00
-- url     : https://prove2.me/theorems/525e9764-bd5e-48d7-8be5-ae2973d31df8
-- title:
--   Theorem 5.2 — adaptive dephasing protocols reduce to Poisson records
-- statement:
--   Let $p$ be any admissible bounded-query forward-evolution protocol with arbitrary measurable classical outcomes, finite-dimensional quantum memory, adaptive nonnegative durations, retained quantum outputs, and joint measurements. Suppose its summed duration is at most $T$ on every complete branch. Fix rates $\Gamma_0,\Gamma_1\ge0$.
--
--   If, on the two dephasing generators $\mathcal L_{\Gamma_0}$ and $\mathcal L_{\Gamma_1}$, the protocol respectively returns YES and NO with probability at least $2/3$, then
--   $$
--   \frac13\le d_{\mathrm{TV}}\!\left(\operatorname{Pois}(\Gamma_0T),
--     \operatorname{Pois}(\Gamma_1T)\right).
--   $$
--
--   The statement packages the simulation in the source proof. A call of duration $t$ is simulated by the phase flips in an interval of a rate-$\Gamma$ Poisson process. Adaptive call boundaries are stopping times relative to that process and independent protocol randomness, and the strong Markov property supplies subsequent increments. Channels on disjoint registers commute, so parallel calls can be sequentialized while retaining summed duration. The entire record is then processed by a $\Gamma$-independent stochastic map.
--
--   Conditional on the event count, ordered event times are order statistics of independent uniform points, independently of $\Gamma$; at rate zero the record is empty. Data processing in both directions therefore replaces record laws by Poisson count laws. Finally, the YES probabilities differ by at least $1/3$, giving the displayed comparison.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.2 proof, 'Reduction to Poisson records' and the output-separation argument, pp.29–30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf

import Definitions.Def_LindbladTolerant_Testing_lower_bound_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace LindbladTolerant.Testing

theorem adaptive_poisson_data_processing {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (p : Protocol n Ω) (T gamma0 gamma1 : ℝ)
    (hp : Admissible p) (hT : TimeAtMost p T)
    (hgamma0 : 0 ≤ gamma0) (hgamma1 : 0 ≤ gamma1)
    (hyes : (2/3 : ℝ≥0∞) ≤ outputProbability p (dephasing n gamma0) true)
    (hno : (2/3 : ℝ≥0∞) ≤ outputProbability p (dephasing n gamma1) false) :
    (1/3 : ℝ) ≤ poissonTV (gamma0 * T) (gamma1 * T) := by sorry
