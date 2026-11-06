-- Prove2me | Theorems.Thm_HMBinPacking_lemma_2
-- name    : HMBinPacking.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:02.95867+00:00
-- url     : https://prove2.me/theorems/a63343a4-df3d-4eb3-9a2d-0b7512e3c6b6
-- title:
--   Lemma 2 — $r+k\,\mathrm{conv}(V)$ has the integer decomposition property for $k\ge d$
-- statement:
--   Let $V\subseteq\mathbb Z^d$ be finite and nonempty, let $k\ge d$ be an integer, and let $r\in\mathbb Z^d$. Then
--   $$
--   r+k\,\mathrm{conv}(V)
--   $$
--   has the integer decomposition property: it is a lattice polytope, and for every integer $n\ge1$ every integer point of $n\,(r+k\,\mathrm{conv}(V))$ is a sum of $n$ integer points of $r+k\,\mathrm{conv}(V)$.
--
--   The dimension $d$ is arbitrary. The bound $k\ge d$ matters: for $k=1$ the property can fail (in dimension $3$). Lemma 4 applies it with $k=d$ to $P_r=r+d\,\mathrm{conv}((S_r-r)/d)$.
--
--   Differences from the source:
--   - encoding: 'has the integer decomposition property', a property defined for lattice polytopes → HasIDP, which includes IsLatticePolytope; reason: the paper's definition applies to lattice polytopes, so the property asserts that r + k conv(V) is one; r + k conv(V) = conv(r + kV) is the convex hull of a finite nonempty subset of Z^d
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 2, p.4

import Mathlib
import Definitions.Def_HMBinPacking_Casts
import Definitions.Def_HMBinPacking_LatticePolytope
open scoped Pointwise

namespace HMBinPacking

/-- **Lemma 2: `r + k conv(V)` has the integer decomposition property for `k ≥ d`.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 2, p.4: "Let V ⊆ Z^d be finite and nonempty, let k ≥ d be
an integer, and let r ∈ Z^d. Then r + k conv(V) has the integer decomposition property."

**Formalization Note.** `R^d` is `Fin d → ℝ` for an arbitrary dimension `d` (not the instance's
`d`); `r + k conv(V)` is the image of `(k : ℝ) • convexHull ℝ V` under translation by `r`. `HasIDP`
includes being a lattice polytope, since the paper defines the property for lattice polytopes. Every
integer `k ≥ d` and every `r ∈ ℤ^d` is allowed. -/
theorem lemma_2 {d : ℕ} (V : Set (Fin d → ℤ)) (hVfin : V.Finite) (hVne : V.Nonempty) (k : ℤ)
    (hk : (d : ℤ) ≤ k) (r : Fin d → ℤ) :
    HasIDP ((fun x => zCast r + x) '' ((k : ℝ) • convexHull ℝ (zCast '' V))) := by sorry

end HMBinPacking
