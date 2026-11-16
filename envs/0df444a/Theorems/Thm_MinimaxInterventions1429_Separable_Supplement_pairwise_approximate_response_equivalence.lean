-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_pairwise_approximate_response_equivalence
-- name    : MinimaxInterventions1429.Separable.Supplement.pairwise_approximate_response_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:16:29.678208+00:00
-- url     : https://prove2.me/theorems/3009ecd4-7cd3-480f-a674-676838d4d20a
-- title:
--   Theorem 1.2 — Pairwise approximate response equivalence
-- statement:
--   Let $m,k\ge2$ and $L,L'\in[0,1]^{m\times k}$. Write $J$ for their joint contrast diameter and $a_Q$ for their least shared-response tolerance. Then
--   $$\frac1{44}\min\{d_q(L,L'),J(L,L')\}\le a_S(L,L')\le\min\{d_q(L,L'),J(L,L')\}.$$
--   For every real linear subspace $U$ strictly containing the separable subspace, with $S_U=\{B\in U:\|B\|_\infty\le16\}$,
--   $$\frac1{34}d_q(L,L')\le a_{S_U}(L,L')\le d_q(L,L').$$
--   All constants are uniform in dimensions, tables and $U$. The statement covers different contrast classes and zero interaction.
--
--   Differences from the source:
--   - encoding: simplex minima and bounded-query suprema → real sInf and sSup on their nonempty bounded ranges; reason: finite dimensions give attained simplex minima and bounded query tolerances
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 1.2, printed p.2 (PDF p.4)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe u_pairwise_approximate_response_equivalence

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem pairwise_approximate_response_equivalence
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (L L' : Table m k) (hL : InCube L) (hL' : InCube L') :
    (min (quotientDist L L') (jointDiameter L L') / 44 ≤
      sharedTolerance {B | Allowed B} L L' ∧
      sharedTolerance {B | Allowed B} L L' ≤ min (quotientDist L L') (jointDiameter L L')) ∧
    ∀ U : Submodule ℝ (Table m k), separableSpace m k < U →
      quotientDist L L' / 34 ≤ sharedTolerance (enlargedQueries U) L L' ∧
      sharedTolerance (enlargedQueries U) L L' ≤ quotientDist L L'  := by sorry

end MinimaxInterventions1429.Separable.Supplement
