-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_exists_half_at_every_maximizer
-- name    : LovaszSchrijver.Defect.exists_half_at_every_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:54:20.164456+00:00
-- url     : https://prove2.me/theorems/4840d9c7-66d1-4139-956c-19304831fcc3
-- title:
--   Lemma 2.12 — some node takes the value ½ at every FRAC-maximizer
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes and let $a \in \mathbb R_+^V$. Assume that
--   $$\max\{a^{\mathsf T}x : x \in \mathrm{STAB}(G)\} < \max\{a^{\mathsf T}x : x \in \mathrm{FRAC}(G)\}.$$
--   Then there exists a node $i \in V$ such that every vector $y \in \mathrm{FRAC}(G)$ maximizing $a^{\mathsf T}x$ has $y_i = \tfrac12$.
--
--   In the proof of Theorem 2.13 this node $i$ is the one whose deletion and contraction lower the defect.
--
--   **Formalization Note** As in Lemma 2.11, the two maxima are numbers $s_S < s_F$ with `IsGreatest` hypotheses.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 182, Lemma 2.12

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem exists_half_at_every_maximizer {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (ha : ∀ i, 0 ≤ a i) (sS sF : ℝ)
    (hS : IsGreatest {s : ℝ | ∃ x ∈ STAB G, s = a ⬝ᵥ x} sS)
    (hF : IsGreatest {s : ℝ | ∃ x ∈ FRAC G, s = a ⬝ᵥ x} sF)
    (hlt : sS < sF) :
    ∃ i : V, ∀ y : V → ℝ, IsFRACMaximizer G a y → y i = 1 / 2 := by sorry

end LovaszSchrijver.Defect
