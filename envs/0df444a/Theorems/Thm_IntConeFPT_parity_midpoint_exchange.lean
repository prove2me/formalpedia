-- Prove2me | Theorems.Thm_IntConeFPT_parity_midpoint_exchange
-- name    : IntConeFPT.parity_midpoint_exchange
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-24T15:07:52.888811+00:00
-- url     : https://prove2.me/theorems/793fb1bd-f296-4689-a890-503c0c328149
-- title:
--   Strict quadratic descent by a parity midpoint exchange
-- statement:
--   In a convex mixed-integer set, suppose two supported generators have distinct integer blocks that agree coordinatewise modulo two. For a cost satisfying discrete Jensen on the projected lattice points, there is a representation of the same aggregate and count, at no greater cost, with strictly smaller multiplicity-weighted sum of squared integer coordinates. Replace one copy of each generator by two copies of their common midpoint; the potential drops by half the squared distance of their integer blocks.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, proof of Lemma 7, pp. 10–11, https://arxiv.org/abs/2609.31328. Local exchange step, not separately numbered.

import Definitions.Def_IntConeFPT_Problem

open IntConeFPT

theorem IntConeFPT.parity_midpoint_exchange {d k : ℕ}
    {P : Set ((Fin d → ℝ) × (Fin k → ℝ))} (hP : Convex ℝ P)
    (f : (Fin d → ℝ) → ℝ)
    (hf : DiscreteJensen {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P}
      (fun x => f (fun i => (x i : ℝ))))
    (μ : Gen d k →₀ ℕ) (hs : (↑μ.support : Set _) ⊆ genSet P)
    {a b : Gen d k} (ha : a ∈ μ.support) (hb : b ∈ μ.support)
    (hne : a.1 ≠ b.1) (hp : ∀ i, a.1 i % 2 = b.1 i % 2) :
    ∃ ν : Gen d k →₀ ℕ, (↑ν.support : Set _) ⊆ genSet P ∧
      aggr ν = aggr μ ∧ count ν = count μ ∧ costOf f ν ≤ costOf f μ ∧
      (ν.sum fun g n => n * ∑ i, (g.1 i).natAbs ^ 2) <
        (μ.sum fun g n => n * ∑ i, (g.1 i).natAbs ^ 2) := by sorry
