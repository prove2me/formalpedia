-- Prove2me | Theorems.Thm_FourBlockIP350_Main_periodic_midpoint
-- name    : FourBlockIP350.Main.periodic_midpoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:02.386651+00:00
-- url     : https://prove2.me/theorems/d66ee9a2-5791-4b8d-8f7c-45f0ab60b47f
-- title:
--   Lemma 4.1 — Periodic midpoint convexity
-- statement:
--   Let $F$ be the finite-box penalized value function, and choose the positive uniform n-fold dilation $N$ for the padded residual system. For every residue $r\in\{0,\ldots,N-1\}^k$, the function
--   $$H_r(v)=F(r+Nv),\qquad v\in\mathbb Z^k,$$
--   is finite everywhere and midpoint-convex. Finiteness is stated as equality with an integer at every argument.
--
--   This is the lattice convexity statement on residue classes modulo $N$.
--
--   Differences from the source:
--   - encoding: N is the positive uniform period supplied by Proposition 2.6 → N > 0 and UniformDilation (3*k) Δbar N; reason: the same upstream property is exposed as a hypothesis to avoid choosing a noncanonical witness; 3*k is the padded block bound used by Theorem 5.2
--   - encoding: integer-valued Hr is midpoint-convex → real projection of the extended-real F, together with integer finiteness at every argument; reason: the conjunction prevents an infinite default projection from supplying the convexity claim
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 8, Lemma 4.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Penalty
import Definitions.Def_FourBlockIP350_Main_Decomposition

namespace FourBlockIP350.Main

open scoped BigOperators

theorem periodic_midpoint {k n Δ N : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hΔ : 0 < Δ) (hN : 0 < N) (hdil : UniformDilation (3*k) Δ N)
    (I : FourBlock k n) (hI : I.localPart.Bounded Δ) (hbox : GoodBox I)
    (r : ZVec k) (hr : IsResidue N r) :
    (∀ v : ZVec k, ∃ t : ℤ, F I (r + (N : ℤ) • v) = ((t : ℝ) : EReal)) ∧
      MidpointConvex (H I N r) := by sorry

end FourBlockIP350.Main
