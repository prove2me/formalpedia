-- Prove2me | Theorems.Thm_IDEPoA_lemma_3_2
-- name    : IDEPoA.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:29.965591+00:00
-- url     : https://prove2.me/theorems/b7227d5a-582f-410d-8bec-56836e5f9d97
-- title:
--   Lemma 3.2: in an acyclic network $Z(\theta)\ge Z(\zeta)+\min\{F^\Delta(\zeta),\theta-\zeta-\tau(P_{\max})\}$, and termination by $\theta_0+\tau(P_{\max})+U$
-- statement:
--   In an acyclic network, every feasible flow $f$ satisfies
--   $$Z(\theta)\ge Z(\zeta)+\min\{F^\Delta(\zeta),\ \theta-\zeta-\tau(P_{\max})\}$$
--   for all times $\theta\ge\zeta\ge0$. That is, as long as there is flow volume in the network at some time $\zeta$, this volume arrives at the sink at most $\tau(P_{\max})$ time steps later at a rate of at least $1$. In particular, every feasible flow in an acyclic network terminates by time $\theta_0+\tau(P_{\max})+U$, that is, $\Theta(f)\le\theta_0+\tau(P_{\max})+U$.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - reading: terminates before θ0 + τ(Pmax) + U → makespan ≤ θ0 + τ(Pmax) + U; reason: the proof concludes 'has terminated by time'; strictness fails for V = {t}, U = 0, where Θ(f) = θ0
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 3.2, p.13

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 3.2 (Graf & Harks, arXiv:2007.07794v2, p.13): in an acyclic network every feasible flow
satisfies `Z(θ) ≥ Z(ζ) + min {F^Δ(ζ), θ − ζ − τ(Pmax)}` for all `θ ≥ ζ ≥ 0`, and terminates by
`θ₀ + τ(Pmax) + U`.

**Formalization Note.** "Terminates before" is `≤`: the proof concludes "has terminated by time",
and strictness fails for `V = {t}`, `U = 0`, where `Θ(f) = θ₀`. `Acyclic` is the published
"no nonempty closed walk". -/
theorem lemma_3_2 (N : FlowNetwork V E) (hN : Standing N) (hac : N.toNetwork.Acyclic) (f : Flow E)
    (hf : IsFeasible N f) :
    (∀ θ ζ : ℝ, 0 ≤ ζ → ζ ≤ θ →
      Z N f θ ≥ Z N f ζ + min (totalLoad f ζ) (θ - ζ - tauPmax N)) ∧
    makespan N f ≤ ENNReal.ofReal (N.θ₀ + tauPmax N + totalVolume N) := by sorry

end IDEPoA
