-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_model_well_defined
-- name    : JSEQDelay.Diffusion.model_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:53.249313+00:00
-- url     : https://prove2.me/theorems/dee3a6e1-58f3-49e1-8245-c951d8416b58
-- title:
--   §3.2, p. 11 — the JSEQ routing rule and the network equations uniquely define the queueing model
-- statement:
--   Fix one network: a delay function $\tau$, an estimator $\Psi$, rates $\lambda>0$, $\mu_k>0$, and positive interarrival and service times $u(i)$, $v_k(i)$. Consider a sample path along which the partial sums $u(1)+\dots+u(m)$ and $v_k(1)+\dots+v_k(m)$ diverge, so that finitely many jobs arrive and finitely many services complete in bounded time. Then there is a pair of queue-length and routed-arrival paths $(q,a)$ satisfying
--   $$q_k(t)=a_k(t)-S_k\Big(\mu_k\int_0^t\mathbf 1\{q_k(s)>0\}ds\Big),\qquad q(0)=a(0)=0,$$
--   together with the JSEQ routing rule (each job joins the queue with the smallest left limit of $\Phi_k(q,a)$ at its arrival epoch, lexicographic ties), and any two such pairs coincide on $[0,\infty)$.
--
--   The page asserts this in one sentence and sketches an induction on the jump times. It guarantees that the network hypothesis of Theorem 4.4 is not vacuous.
--
--   **Formalization Note** Uniqueness is on $[0,\infty)$, since values at negative times are never constrained. The estimator acts on real-valued paths and the routing rule uses left limits of the estimated queue lengths at the arrival epochs (see the `Model` definition).
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 11, §3.2, 'Along with the equations introduced in Section 2.1, this uniquely defines the queueing model'

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_JSEQDelay_Diffusion_Model

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy

/-- **§3.2, p. 11: the JSEQ network is well defined.** For a delay function `τ`, an estimator
`Ψ`, positive rates `λ`, `μ_k` and positive interarrival and service times, every sample path
`ω` along which the arrival and service partial sums diverge carries exactly one pair of queue
length and routed arrival paths `(q, a)` satisfying the network equations (6)–(8) and the JSEQ
routing rule (unique on `[0, ∞)`). -/
theorem model_well_defined {K : ℕ} (hK : 2 ≤ K) {Ω : Type*}
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ)
    (hu : ∀ i ω, 0 < u i ω) (hv : ∀ k i ω, 0 < v k i ω)
    (lam : ℝ) (mu : Fin K → ℝ) (hlam : 0 < lam) (hmu : ∀ k, 0 < mu k)
    (τ : ℝ → Fin K → ℝ) (hτ : DelayFunction τ)
    (Ψ : Path K → Path K → Path K) (hΨ : IsEstimator τ Ψ)
    (ω : Ω) (hω : GoodPath u v ω) :
    (∃ q a : Path K, IsJSEQPath u v lam mu τ Ψ ω q a) ∧
    ∀ q a q' a' : Path K, IsJSEQPath u v lam mu τ Ψ ω q a →
      IsJSEQPath u v lam mu τ Ψ ω q' a' → ∀ t, 0 ≤ t → q t = q' t ∧ a t = a' t := by sorry

end JSEQDelay.Diffusion
