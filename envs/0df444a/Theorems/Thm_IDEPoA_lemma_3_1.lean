-- Prove2me | Theorems.Thm_IDEPoA_lemma_3_1
-- name    : IDEPoA.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:21.100443+00:00
-- url     : https://prove2.me/theorems/911ea59f-e5bc-4d79-a55a-e1cf997bf1af
-- title:
--   Lemma 3.1: volume $\lambda$ leaves an edge within $\lambda/\nu_e+\tau_e$
-- statement:
--   Let $f$ be a feasible flow, $\theta_1\ge0$, $e$ an edge, and $0\le\lambda\le F_e^\Delta(\theta_1)$. With $\theta_2=\theta_1+\lambda/\nu_e+\tau_e$, the cumulative outflow of $e$ between $\theta_1$ and $\theta_2$ is at least $\lambda$:
--   $$F_e^-(\theta_2)-F_e^-(\theta_1)\ge\lambda.$$
--
--   This gives an upper bound on the time a given volume of flow can stay on one edge, and is used throughout the extension of sink-like subgraphs.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 3.1, p.12

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 3.1 (Graf & Harks, arXiv:2007.07794v2, p.12): flow volume `λ ≤ Fₑ^Δ(θ₁)` leaves the edge
`e` by time `θ₂ = θ₁ + λ/νₑ + τₑ`. -/
theorem lemma_3_1 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (θ₁ : ℝ) (hθ₁ : 0 ≤ θ₁) (e : E) (lam : ℝ) (hlam : 0 ≤ lam) (hlam' : lam ≤ load f e θ₁) :
    Fminus f e (θ₁ + lam / N.ν e + N.τ e) - Fminus f e θ₁ ≥ lam := by sorry

end IDEPoA
