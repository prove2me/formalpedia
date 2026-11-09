-- Prove2me | Theorems.Thm_FourBlockIP350_Main_optimization_period
-- name    : FourBlockIP350.Main.optimization_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:10.472971+00:00
-- url     : https://prove2.me/theorems/40780c35-0131-431a-be9b-349aeea78b55
-- title:
--   Corollary 4.3 — The optimization period
-- statement:
--   For a finite nonempty box and the positive n-fold dilation $N$, put $M=kN$. For every integer vector $q$, not only canonical residues, the function
--   $$F_q(v)=F(q+Mv),\qquad v\in\mathbb Z^k,$$
--   has an everywhere finite convex extension to $\mathbb R^k$.
--
--   The factor $k$ in the optimization period is retained. This is the convex-extensibility statement used for residue optimization.
--
--   Differences from the source:
--   - encoding: N is the positive uniform period supplied by Proposition 2.6 → N > 0 and UniformDilation (3*k) Δbar N; reason: the same upstream property is exposed as a hypothesis to avoid choosing a noncanonical witness; 3*k is the padded block bound used by Theorem 5.2
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 13, Corollary 4.3

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Penalty
import Definitions.Def_FourBlockIP350_Main_Decomposition

namespace FourBlockIP350.Main

open scoped BigOperators

theorem optimization_period {k n Δ N : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hΔ : 0 < Δ) (hN : 0 < N) (hdil : UniformDilation (3*k) Δ N)
    (I : FourBlock k n) (hI : I.localPart.Bounded Δ) (hbox : GoodBox I)
    (q : ZVec k) : ConvexExtensible (Fq I N q) := by sorry

end FourBlockIP350.Main
