-- Prove2me | Theorems.Thm_HMBinPacking_rational_strong_separation_answers
-- name    : HMBinPacking.rational_strong_separation_answers
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:16:43.58721+00:00
-- url     : https://prove2.me/theorems/90490ae2-2bad-491c-93c1-1f3115bc7485
-- title:
--   Lemmas 7–8, rational strong-separation certificates for the residue and packing polytopes
-- statement:
--   Let $I$ be a high-multiplicity bin packing instance with $d$ item types. For each residue $r$, let $P_r$ be the convex hull of its integer bin configurations. Let $K$ be the joint packing polytope, in the paper's $D=(d+1)d^d$ flat coordinates. For $Q=P_r$ and for $Q=K$, every rational query $y$ has a strong-separation certificate. This is either a membership certificate or rational coefficients $u,\alpha$ satisfying
--   $$\forall x\in Q,\quad u^\top x\leq \alpha < u^\top y.$$
--   The conclusion applies to empty and lower-dimensional polytopes. It establishes the geometric correctness requirements of the residue and packing separation oracles.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 8, p.5. Geometric or encoding subclaim from the proof of Lemma 8.

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Theorems.Thm_HMBinPacking_cone_separation_from_one_residue_answer
import Mathlib.Algebra.BigOperators.Option
open HMBinPacking Finset

namespace HMBinPacking

theorem rational_strong_separation_answers (I : Instance) :
    (∀ (r : Fin I.d → Fin I.d) (y : Fin I.d → ℚ),
      ∃ w, IsSepAnswer (Pr I r) y w) ∧
    ∀ y : Fin (D I) → ℚ, ∃ w, IsSepAnswer (KFlat I) y w := by sorry

end HMBinPacking
