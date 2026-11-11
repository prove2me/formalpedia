-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_observation_1
-- name    : LiuHelsenDesigns.OneD.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:05.38196+00:00
-- url     : https://prove2.me/theorems/febe87e0-240e-45f7-9d8e-4cacdc38b0ef
-- title:
--   Observation 1 — constant-size local routing
-- statement:
--   Fix positive cell width b and interaction range r, and a participation bound p. There is a depth bound D depending only on these constants. For every open chain and every layer of disjoint local gates whose supports meet at most r adjacent b-wire cells, with each cell participating at most p times,
--
--   $$
--   \exists C:\quad\operatorname{eval}(C)=\operatorname{eval}(\text{layer}),\qquad D(C)\le D.
--   $$
--
--   The output uses only one-wire or adjacent two-wire unitary gates on the same physical register. No arbitrary wire permutation is free.
--
--   Differences from the source:
--   - encoding: a layer of constant-local gates in bounded adjacent cells → a disjoint-support layer of actual placed unitaries with explicit cell-width, range and participation parameters; reason: layer has its usual simultaneous-gate meaning; output is an exact circuit on the same physical wires
--   - generalization: constant-local gates including CNOT and Toffoli, with 18-bit cells in the construction → arbitrary unitary gates supported on a bounded number of cells of any fixed positive width; reason: the source gates and 18-bit cells are instances; a fixed-size unitary admits an exact finite decomposition into one- and two-wire unitaries, and all placement and participation bounds are retained
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 31, Observation 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_routing

namespace LiuHelsenDesigns.OneD
theorem observation_1 (b r p : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    ∃ D : ℕ, ∀ n : ℕ, ∀ gs : List (PlacedUnitary n), boundedCellLayer b r p gs →
      ∃ cs : List (List (PlacedUnitary n)), cs.length ≤ D ∧
        placedCircuitMatrix cs = placedLayerMatrix gs ∧
        ∀ layer ∈ cs, DisjointLayer layer ∧ ∀ g ∈ layer, nearestGate g := by sorry
end LiuHelsenDesigns.OneD
