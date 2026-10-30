-- Prove2me | Theorems.Thm_OnDemandRideHailing_CallNoCall_proof_theorem_4_wait_antitone_rates
-- name    : OnDemandRideHailing.CallNoCall.proof_theorem_4_wait_antitone_rates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:01:23.350964+00:00
-- url     : https://prove2.me/theorems/b1fb3d9f-6857-4ce0-bcea-5fc9e036cf09
-- title:
--   Proof of Theorem 4: in a state-dependent M/M/k queue, raising the service rate in every state does not lengthen the average waiting time
-- statement:
--   Let $\lambda\ge0$ and let $\mu,\mu'$ be service-rate sequences with $0<\mu_i\le\mu'_i$ for every state $i\ge1$. Write $\mathcal W(\lambda,s,\mu)\in(-\infty,+\infty]$ for the average waiting time of the state-dependent M/M/k queue (the p. 34 formula when stable, $+\infty$ otherwise). Then
--
--   1. $\mathcal W(\lambda,s,\mu')\le\mathcal W(\lambda,s,\mu)$;
--   2. if moreover the queue with rates $\mu$ is stable and $\mu_i<\mu'_i$ for every $i\ge1$, then $\mathcal W(\lambda,s,\mu')<\mathcal W(\lambda,s,\mu)$.
--
--   In particular, if the $\mu$-queue is stable then so is the $\mu'$-queue. This is the step of the proof of Theorem 4 that turns the comparison of service rates into a comparison of waiting times.
--
--   Differences from the source:
--
--   - generalization: the rates of the approximated call and no-call systems ('the no-call system has a higher service rate … for any system state') → arbitrary rate sequences µ, µ' with 0 < µ_i ≤ µ'_i (clause 2: µ_i < µ'_i) for every i ≥ 1, any λ ≥ 0, any shift s; reason: the step is a property of any state-dependent M/M/k queue, as the proof itself says; it specializes to µ = µ(1c), µ' = µ(nc), s = d/v
--   - encoding: the average waiting time W of the approximating M/M/k queue, given on p. 34 by Σ_{i≥1} iλ^{i−1}/(µ1⋯µi) / (1 + Σ_{i≥1} λ^i/(µ1⋯µi)) − d/v, with W = ∞ when the queue is not stable → avgWait: the same formula (numerator reindexed i ↦ i+1) as an EReal when both series are summable, ⊤ otherwise; reason: the paper takes the formula from standard queueing theory and uses exactly this ∞ convention (p. 34); no CTMC or Little's law is formalized
--   - reading: 'this implies the average waiting time in the no-call system is shorter' → clause 1: ≤ in EReal when µ ≤ µ'; clause 2: < when moreover µ < µ' in every state and the µ-queue is stable; reason: with µ = µ' nothing is shorter, so the non-strict comparison is the general one; when the µ-queue is unstable both waiting times may be +∞, so the strict clause needs stability
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, proof of Theorem 4, unnumbered step, p. 38

import Mathlib
import Definitions.Def_OnDemandRideHailing_CallNoCall_QueueStable
import Definitions.Def_OnDemandRideHailing_CallNoCall_waitFormula
import Definitions.Def_OnDemandRideHailing_CallNoCall_avgWait

namespace OnDemandRideHailing.CallNoCall

/-- **Proof of Theorem 4: raising the service rate in every state does not lengthen the average
waiting time.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, proof of Theorem 4, p. 38: "That is, the approximated one-direction no-call
system has a higher service rate compared to the approximated one-direction call system for any
system state. Now we show that this implies the average waiting time in the no-call system is
shorter."

Let `λ ≥ 0` and let `µ, µ'` be service-rate sequences with `0 < µ_i ≤ µ'_i` for every state
`i ≥ 1`. Then
1. the average waiting time with rates `µ'` is at most that with rates `µ`, as extended reals
   (if the `µ`-queue is unstable its waiting time is `+∞`; if it is stable, the `µ'`-queue is
   stable too and its waiting-time formula is no larger);
2. if moreover the `µ`-queue is stable and `µ_i < µ'_i` for every `i ≥ 1`, the waiting time with
   rates `µ'` is strictly shorter.

**Formalization Note.** The paper derives this step from `∂W/∂µm < 0` coordinate by coordinate;
since infinitely many coordinates change at once, the step is stated as the comparison itself,
for arbitrary positive rate sequences, with the `+∞` convention of p. 34. "Shorter" is the strict
clause 2; it needs the `µ`-queue to be stable, since otherwise both waiting times may be `+∞`. -/
theorem proof_theorem_4_wait_antitone_rates {lam s : ℝ} {μ μ' : ℕ → ℝ}
    (hlam : 0 ≤ lam) (hμ : ∀ i, 1 ≤ i → 0 < μ i) (hle : ∀ i, 1 ≤ i → μ i ≤ μ' i) :
    avgWait lam s μ' ≤ avgWait lam s μ ∧
      (QueueStable lam μ → (∀ i, 1 ≤ i → μ i < μ' i) → avgWait lam s μ' < avgWait lam s μ) := by sorry

end OnDemandRideHailing.CallNoCall
