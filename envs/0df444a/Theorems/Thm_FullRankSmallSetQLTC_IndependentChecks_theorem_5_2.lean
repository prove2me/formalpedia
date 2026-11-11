-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_theorem_5_2
-- name    : FullRankSmallSetQLTC.IndependentChecks.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:58.026983+00:00
-- url     : https://prove2.me/theorems/8763decd-7ed0-480b-acf9-76d0b8ab93ab
-- title:
--   Theorem 5.2 — full-rank lossless expanders on the 2-groups G_m
-- statement:
--   For every integer $t\ge1$, every $\varepsilon\in(0,1)$ and every positive integer $a_{\min}$ there are positive integers $u$ and $a\ge a_{\min}$, a constant $c>0$ and an integer $m_0\ge3$ such that for every $m\ge m_0$ there is a simple bipartite graph
--   $$Z_m=(G_m\times[tu],\ G_m\times[u],\ E_m)$$
--   with degrees $(a,ta)$, two-sided $(c,\varepsilon)$-lossless, whose binary adjacency map $\mathbb F_2^{G_m\times[tu]}\to\mathbb F_2^{G_m\times[u]}$ has full row rank. Left translation is a free $G_m$-action. Neighbours on either side can be enumerated in time polynomial in $m=O(\log|G_m|)$.
--
--   This is the precise form of Theorem 1.1 and the input to the balanced product.
--
--   Differences from the source:
--   - encoding: neighbours can be enumerated in time polynomial in m → fixed machines (chosen with u, a, c, m₀ and the family) list the normal-form codes of the neighbours of a vertex, in each direction, for all m ≥ m₀; reason: the enumeration is uniform in m, as the clause requires; vertices are input by their normal-form codes
--   - encoding: left translation is a free G_m-action → left translation is free on both vertex sets and preserves the edges; reason: an action on a graph preserves its edges
--   - encoding: the graphs Z_m on G_m for every m ≥ m₀ → 3 ≤ m₀, with the graph properties and algorithms for all m ≥ m₀; reason: the source defines G_m for m ≥ 3 (p. 18); p. 25 inherits the threshold from Theorem 5.1
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 5.2, p. 25 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Explicit
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Quaternion

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open Classical in
/-- **Theorem 5.2** (Full-rank lossless expanders, precise form of Theorem 1.1, p. 25). For every
integer `t ≥ 1`, every `ε ∈ (0, 1)` and every positive integer `a_min` there are positive
integers `u`, `a ≥ a_min`, a constant `c > 0` and an integer `m₀ ≥ 3` such that for every `m ≥ m₀`
there is a simple bipartite graph `Z_m = (G_m × [tu], G_m × [u], E_m)` with degrees `(a, ta)`,
two-sided `(c, ε)`-lossless, whose binary adjacency map `𝔽₂^{G_m × [tu]} → 𝔽₂^{G_m × [u]}` has
full row rank, on which left translation is a free `G_m`-action (preserving edges); and the
neighbours on either side can be enumerated by fixed machines in time polynomial in `m`
(on the normal-form codes of `G_m × [n]`). -/
theorem theorem_5_2 (t : ℕ) (ht : 1 ≤ t) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) (amin : ℕ)
    (hamin : 0 < amin) :
    ∃ (u a : ℕ) (c : ℝ) (m₀ : ℕ)
      (Z : ∀ m, Cell ↥(Gm m) (Fin (t * u)) → Cell ↥(Gm m) (Fin u) → Prop),
      0 < u ∧ 0 < a ∧ amin ≤ a ∧ 0 < c ∧ 3 ≤ m₀ ∧
      (∀ m, m₀ ≤ m →
        IsTwoSidedLossless (Z m) a (t * a) c ε ∧
        (adjMatrix (Z m)).rank = Fintype.card (Cell ↥(Gm m) (Fin u)) ∧
        IsInvariantRel ↥(Gm m) (Z m) ∧
        IsFreeAction ↥(Gm m) (Cell ↥(Gm m) (Fin (t * u))) ∧
        IsFreeAction ↥(Gm m) (Cell ↥(Gm m) (Fin u))) ∧
      (∃ f, PolyTimeFn f ∧
        EnumeratesNbrs (fun m (v : Cell ↥(Gm m) (Fin (t * u))) => gmCellCode m v)
          (fun m (v : Cell ↥(Gm m) (Fin u)) => gmCellCode m v) Z m₀ f) ∧
      (∃ f, PolyTimeFn f ∧
        EnumeratesNbrs (fun m (v : Cell ↥(Gm m) (Fin u)) => gmCellCode m v)
          (fun m (v : Cell ↥(Gm m) (Fin (t * u))) => gmCellCode m v)
          (fun m r ℓ => Z m ℓ r) m₀ f) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
