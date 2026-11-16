-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_residue_convex_extensible
-- name    : FourBlockIP350.Main.Supplement.residue_convex_extensible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:10:01.417725+00:00
-- url     : https://prove2.me/theorems/bf8a41b5-00b3-41f9-80c5-3ac0f16334c7
-- title:
--   Corollary B.6 — Convex extensibility of $F_K$ on residue classes modulo $M=kN$
-- statement:
--   Under the assumptions of Lemma B.5 ($k,n\ge1$, local blocks bounded by $\bar\Delta\ge1$, finite integral bounds with nonempty intervals, separable convex $\Phi$, and a positive $N$ with the uniform dilation property for blocks of size $2k$), let $M=kN$. For every real $K>0$ and every $q\in\mathbb Z^k$, the function
--   $$v\mapsto F_K(q+Mv),\qquad v\in\mathbb Z^k,$$
--   is convex extensible: there is a convex function $G:\mathbb R^k\to\mathbb R$ with $G(v)=F_K(q+Mv)$ for every $v\in\mathbb Z^k$.
--
--   This makes the penalized value function on each residue class modulo $M$ a valid input for discrete convic minimization.
--
--   Differences from the source:
--   - generalization: N is the positive integer provided by Proposition 2.6 for Q = [E I] → every N > 0 with UniformDilation (2*k) Δbar N; reason: the N of Proposition 2.6 (published uniform_idp at block size 2k) has this property, so the statement specializes to the source's
--   - encoding: Δbar is the largest absolute entry of the blocks B, D → any Δ ≥ 1 bounding those entries; reason: Δbar ≥ 1 is a standing assumption (p. 2); the statement at Δ = Δbar is the source's
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 25, Corollary B.6

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Supplement_SeparableIP
import Definitions.Def_FourBlockIP350_Main_Decomposition

open scoped BigOperators

namespace FourBlockIP350.Main.Supplement

open FourBlockIP350.Main

/-- Corollary B.6, p. 25: with `M = kN`, for every real `K > 0` and every `q ∈ ℤ^k`,
`v ↦ F_K(q + M v)` is convex extensible. -/
theorem residue_convex_extensible {k n Δ N : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hΔ : 0 < Δ) (hN : 0 < N) (hdil : UniformDilation (2 * k) Δ N)
    (I : FourBlock k n) (hI : I.localPart.Bounded Δ) (hbox : GoodBox I)
    (φ : BlockCol k n → ℝ → ℝ) (hφ : SeparableConvex φ)
    (K : ℝ) (hK : 0 < K) (q : ZVec k) :
    ConvexExtensible (fun v : ZVec k => (FK I φ K (q + (period k N : ℤ) • v)).toReal) := by sorry

end FourBlockIP350.Main.Supplement
