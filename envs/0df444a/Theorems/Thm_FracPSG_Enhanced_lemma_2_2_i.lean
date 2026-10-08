-- Prove2me | Theorems.Thm_FracPSG_Enhanced_lemma_2_2_i
-- name    : FracPSG.Enhanced.lemma_2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:31.698894+00:00
-- url     : https://prove2.me/theorems/1ad1f3ad-3261-44cd-8482-82bb03a93dfd
-- title:
--   Lemma 2.2(i) — the limiting subdifferential of h + ι_S is closed and convex for weakly convex h
-- statement:
--   Let $S$ be a nonempty closed convex subset of a finite-dimensional real Hilbert space $H$, and let $h: H\to(-\infty,+\infty]$ be proper, lower semicontinuous and weakly convex on $S$ (that is, $h+\iota_S+\frac\rho2\|\cdot\|^2$ is convex for some $\rho\ge0$). Then for all $x\in H$,
--   $$\partial_L(h+\iota_S)(x)\ \text{is a (possibly empty) closed convex set.}$$
--
--   In the proof of Theorem 6.1(iii) this turns the inclusion of every active gradient into an inclusion of their convex hull, which is the limiting subdifferential of the max-type denominator.
--
--   **Formalization Note** Weak convexity of an extended-real-valued function is stated through convexity of the epigraph of $h+\iota_S+\frac\rho2\|\cdot\|^2$. The source's hypothesis "$\bar x\in S$" is not used by part (i) and is replaced by $S\ne\emptyset$.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 5, Lemma 2.2(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Enhanced_Basic

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Enhanced

open NonconvexSplitting.Shared

/-- Lemma 2.2(i) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 5): let `S` be a nonempty closed convex set
and `h : H → (−∞, +∞]` proper, lower semicontinuous and weakly convex on `S`. Then for every `x`,
`∂_L(h + ι_S)(x)` is a (possibly empty) closed convex set. -/
theorem lemma_2_2_i {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {h : EuclideanSpace ℝ (Fin N) → EReal}
    (hSne : S.Nonempty) (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hprop : IsProperFn h) (hlsc : LowerSemicontinuous h)
    (hwc : ∃ ρ : ℝ, IsWeaklyConvexOnE S h ρ) (x : EuclideanSpace ℝ (Fin N)) :
    IsClosed (LimitingSubdiff (FracPSG.Subseq.addInd h S) x) ∧ Convex ℝ (LimitingSubdiff (FracPSG.Subseq.addInd h S) x) := by sorry

end FracPSG.Enhanced
