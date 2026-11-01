-- Prove2me | Theorems.Thm_IDEPoA_queue_facts
-- name    : IDEPoA.queue_facts
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:06.192881+00:00
-- url     : https://prove2.me/theorems/ed378d40-d51e-4466-a11c-2733a67e1191
-- title:
--   Queues and loads are nonnegative, $c_e\ge\tau_e$, and $F_e^+(\theta)=F_e^-(\theta+c_e(\theta))$
-- statement:
--   Let $f$ be a feasible flow, $e$ an edge and $\theta\ge0$. Then
--   $$q_e(\theta)\ge0,\qquad F_e^\Delta(\theta)\ge0,\qquad c_e(\theta)\ge\tau_e,\qquad F_e^+(\theta)=F_e^-\bigl(\theta+c_e(\theta)\bigr).$$
--
--   The last identity says that a particle entering $e$ at time $\theta$ leaves it at time $\theta+c_e(\theta)$, and so justifies calling $c_e$ the travel time. These facts underlie every later computation.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - generalization: ce(θ) ∈ R>0 in the list of symbols (p.39) → τe ≤ ce(θ); reason: implies positivity, as τe ≥ 1
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, App. A, p.39; App. B, proof of Claim 6, property (a), p.40

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Elementary properties of a feasible flow (Graf & Harks, arXiv:2007.07794v2, App. A, p.39:
"qₑ(θ) ∈ ℝ≥0" and "Fₑ^Δ(θ) ∈ ℝ≥0"; App. B, proof of Claim 6, p.40, property (a)): for every edge and
`θ ≥ 0` the queue and the load are nonnegative, `cₑ(θ) ≥ τₑ`, and `Fₑ⁺(θ) = Fₑ⁻(θ + cₑ(θ))`. The
paper takes (a) from Sering's thesis [35, Lemma 3.1]. -/
theorem queue_facts (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (e : E) (θ : ℝ) (hθ : 0 ≤ θ) :
    0 ≤ queue N f e θ ∧ 0 ≤ load f e θ ∧ (N.τ e : ℝ) ≤ cost N f e θ ∧
      Fplus f e θ = Fminus f e (θ + cost N f e θ) := by sorry

end IDEPoA
