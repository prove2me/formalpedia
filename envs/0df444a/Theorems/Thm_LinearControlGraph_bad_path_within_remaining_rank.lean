-- Prove2me | Theorems.Thm_LinearControlGraph_bad_path_within_remaining_rank
-- name    : LinearControlGraph.bad_path_within_remaining_rank
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T20:02:15.804798+00:00
-- url     : https://prove2.me/theorems/ea7b1df6-9781-4e2e-a51d-dacf47232772
-- title:
--   Short witnesses to nonzero observations in linear control graphs
-- statement:
--   Let a finite directed control graph have $c$ locations. A state stores a vector in a common $d$-dimensional vector space over a field, and each edge offers one or more linear updates available on all states at its source. Each location has an arbitrary set of starting vectors and a linear observation. Let $r$ be the sum, over locations, of the dimensions of the spans of the starting sets. If any finite path attains a nonzero observation, some path of length at most $cd-\max(1,r)$ does. Subtraction is truncated at zero. The formal statement accumulates all states reachable within each step bound.
-- source:
--   The proof uses the reachable-span method for weighted automata. See Tzeng, A Polynomial-Time Algorithm for the Equivalence of Probabilistic Automata, SIAM Journal on Computing 21(2), 1992, https://doi.org/10.1137/0221017. Here the proof uses a separate subspace at each control location and keeps track of the initial total rank.

import Mathlib

theorem LinearControlGraph.bad_path_within_remaining_rank {K V W ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [Fintype ι]
    (edge : ι → ι → Set (Module.End K V)) (seed : ι → Set V)
    (probe : ι → V →ₗ[K] W) :
    let reachable : ℕ → ι → Set V :=
      Nat.rec seed (fun _ previous j =>
        previous j ∪ ⋃ i, ⋃ f : edge i j, f.val '' previous i)
    let initialRank := ∑ i, Module.finrank K (Submodule.span K (seed i))
    (∃ n i x, x ∈ reachable n i ∧ probe i x ≠ 0) ↔
      ∃ i x, x ∈ reachable (Fintype.card ι * Module.finrank K V - max 1 initialRank) i ∧
        probe i x ≠ 0 := by sorry
