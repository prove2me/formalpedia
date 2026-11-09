-- Prove2me | Theorems.Thm_FourBlockIP350_Main_finite_envelope
-- name    : FourBlockIP350.Main.finite_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:23.441995+00:00
-- url     : https://prove2.me/theorems/c4280783-86f0-4026-b6ed-0e5f45ad43f4
-- title:
--   Claim 4.2.4 — Finite convex envelope
-- statement:
--   For an everywhere finite midpoint-convex $h:\mathbb Z^k\to\mathbb R$, with $k\ge1$, form $C$ using all finite convex representations on $k\mathbb Z^k$. Then
--   $$-\infty<C(z)<+\infty\quad(z\in\mathbb R^k),\qquad C|_{k\mathbb Z^k}=h|_{k\mathbb Z^k},$$
--   and the resulting real-valued function is convex on the whole real space.
--
--   No lower-bound or attainment premise is imposed on the representing costs: finiteness is part of this claim. It supplies a finite convex extension on the coarser lattice.
--
--   Differences from the source:
--   - encoding: C has codomain R union {−infinity} → C is first defined in EReal, with both infinities excluded in the conclusion; reason: an unchecked real infimum would silently default to zero; the extra representable +infinity is ruled out rather than assumed away
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 12, Claim 4.2.4

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem finite_envelope {k : ℕ} (hk : 0 < k) (h : ZVec k → ℝ)
    (hh : MidpointConvex h) :
    (∀ z : RVec k, ConvexEnvelope h z ≠ ⊥ ∧ ConvexEnvelope h z ≠ ⊤) ∧
    ConvexOn ℝ Set.univ (fun z => (ConvexEnvelope h z).toReal) ∧
    ∀ z ∈ CoarseLattice k, ConvexEnvelope h (realVec z) = (h z : EReal) := by sorry

end FourBlockIP350.Main
