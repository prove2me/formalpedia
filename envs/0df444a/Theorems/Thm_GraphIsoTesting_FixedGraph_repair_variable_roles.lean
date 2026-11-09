-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_repair_variable_roles
-- name    : GraphIsoTesting.FixedGraph.repair_variable_roles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:38:48.879266+00:00
-- url     : https://prove2.me/theorems/f21daa8a-0f23-437a-8461-8605cdfd39b4
-- title:
--   Claim 3.4 — Recovering the variable roles
-- statement:
--   Fix an exact $(3,6)$ matrix $A$ and any vector $b$. For every vertex bijection $\pi:V(G_0)\to V(G_b)$ there is a role-preserving bijection $\mu$ such that
--
--   $$\Delta_b(\mu)\le(1+4d)\Delta_b(\pi),\qquad d=13.$$
--
--   Role preservation concerns the entire variable-anchor and value classes only; it may split variable gadgets and places no condition on constraint roles. The starting bijection is unrestricted. This is the first of the source's two repair statements, retaining its exact factor $1+4d=53$.
--
--   Differences from the source:
--   - generalization: the fixed matrix supplied by Lemma 2.3 in the section 3 preamble → every binary matrix with exact row weight three and column weight six; reason: the structural results use only the exact weights and distinct nonzero columns; the source matrices satisfy these conditions
--   - encoding: parity-dependent assignment labels and arbitrary fixed row orderings → b-independent even-assignment labels interpreted as α + bⱼ, with increasing row and occurrence orderings; reason: this is the fixed-label oracle convention of section 3.3 and a permitted choice of fixed orderings; graphs remain uncolored and all bijections are allowed
--   - encoding: d is the constructed graphs maximum degree bound → the factor is 1 + 4 * 13; reason: the size and degree paragraph on p. 9 supplies d = 13
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 13, Claim 3.4

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_ParityGadget

namespace GraphIsoTesting.FixedGraph

theorem repair_variable_roles {m k : ℕ} (A : BinaryMatrix m k) (h : Sparse36 A)
    (b : Fin m → Bit) (π : Equiv.Perm (GadgetVertex m k)) :
    ∃ μ : Equiv.Perm (GadgetVertex m k), RolePreserving μ ∧
      gadgetMismatch A h b μ ≤ (1 + 4 * 13) * gadgetMismatch A h b π := by sorry

end GraphIsoTesting.FixedGraph
