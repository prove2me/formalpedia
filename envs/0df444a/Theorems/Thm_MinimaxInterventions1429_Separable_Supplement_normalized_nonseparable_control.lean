-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_normalized_nonseparable_control
-- name    : MinimaxInterventions1429.Separable.Supplement.normalized_nonseparable_control
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:15:27.452957+00:00
-- url     : https://prove2.me/theorems/ff396bda-bdab-487e-a2ad-e405c7b8b4a9
-- title:
--   Lemma 5.2 — A normalized nonseparable control
-- statement:
--   Let $m,k\ge2$ and let $U$ be any real linear subspace strictly containing the separable subspace. There is a public control $C\in U$ satisfying
--   $$C_{g1}=0,\qquad\|C\|_\infty=1,\qquad\Lambda(C)=2.$$
--   For $K=\{tC:|t|\le1\}$, its available interaction is $\Xi(K)=2$, and $Q_K\subseteq S_U$ at $\tau=1$. This supplies a uniformly normalized control for every strict enlargement, with no dimension-dependent constants.
--
--   Differences from the source:
--   - encoding: a normalized public matrix → an existential matrix with its literal segment and query inclusion; reason: public means independent of unknown tables; no control is assumed to exist
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 5.2, printed p.17 (PDF p.19)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe u_normalized_nonseparable_control

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem normalized_nonseparable_control
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (U : Submodule ℝ (Table m k)) (hU : separableSpace m k < U) :
    ∃ C : Table m k, C ∈ U ∧ (∀ g, C g 0 = 0) ∧ entryNorm C = 1 ∧
      interaction C = 2 ∧ availableInteraction (segmentControl C) = 2 ∧
      controlQueries (segmentControl C) 1 ⊆ enlargedQueries U := by sorry

end MinimaxInterventions1429.Separable.Supplement
