-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_exact_response_equivalence
-- name    : MinimaxInterventions1429.Separable.Supplement.exact_response_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:18:34.131908+00:00
-- url     : https://prove2.me/theorems/53606e47-0cef-4b3f-b99c-0fcc2ee97f7e
-- title:
--   Theorem 3.8 — Exact response equivalence
-- statement:
--   For $m,k\ge2$ and cube tables $L,L'$, the following three conditions are equivalent:
--   1. One map is exactly optimal for both tables after every bounded separable surcharge in $S$.
--   2. One map is exactly optimal for both after every real separable surcharge.
--   3. Their contrasts agree and either their difference is a common scalar matrix or their interaction is zero:
--   $$\omega(L)=\omega(L')\quad\text{and}\quad\bigl(L-L'=c\mathbf1\text{ for some }c\in\mathbb R\ \text{or}\ \Lambda(L)=0\bigr).$$
--   This identifies the exact ambiguity on the closed cube, including boundary and additive tables; uniqueness of minimizers is not required.
--
--   Differences from the source:
--   - encoding: three equivalent conditions and maps on query subtypes → two linked iff statements and total maps restricted by query membership; reason: extension outside the specified query set changes no response instance
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 3.8, printed p.14 (PDF p.16)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe u_exact_response_equivalence

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem exact_response_equivalence
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (L L' : Table m k) (hL : InCube L) (hL' : InCube L') :
    (CommonResponse {B | Allowed B} L L' 0 ↔ CommonResponse {B | IsSeparable B} L L' 0) ∧
    (CommonResponse {B | IsSeparable B} L L' 0 ↔
      contrasts L = contrasts L' ∧ ((∃ c : ℝ, L-L' = fun _ _ => c) ∨ interaction L = 0)) := by sorry

end MinimaxInterventions1429.Separable.Supplement
