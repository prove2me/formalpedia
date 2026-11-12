-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_28
-- name    : LocalSweepFT.claim_4_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:53.836923+00:00
-- url     : https://prove2.me/theorems/e8ab1eb1-2363-4864-8bf4-d40e1b29e6b5
-- title:
--   Claim 4.28 — every syndrome vertex after a sweep step is caused by a nearby earlier syndrome vertex
-- statement:
--   Let $d'\ge2$, $d-d'\ge2$, let $\mathrm{rule}$ be any sweep rule on $\mathcal T^d_\infty$, $z$ a finitely supported $d'$-chain and $\xi$ the chain after one parallel application of the rule. For every vertex $v$ of $\partial^-\xi$ and every potential wall $L_i$ there are a vertex $u$ of $\partial^-z$ and a $d'$-cell $f$ containing both $u$ and $v$ such that
--   $$L_i(u)\ge L_i(v)\ (i\le d),\qquad L_{d+1}(u)>L_{d+1}(v).$$
--
--   These are the predecessor arrows of the Toom contour: they place the space–time history of the syndrome into a space–time graph with the potential inequality used in §5.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - generalization: z a finite chain (Def 4.22) → every finitely supported d′-chain of ℤ^d; reason: finite chains in the sense of Def 4.22 are a special case
--   - reading: "the sweep rule" → every sweep rule (IsSweepRule ℤ); reason: the proof uses only the sweep-rule conditions
--   - encoding: "there is a vertex u … for i ≠ d + 1 … if i = d + 1" → for each wall i a vertex u and a face f (which may depend on i); reason: the proof chooses u per wall
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.28, p.31

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT
import Definitions.Def_LocalSweepFT_IsSweepRule

namespace LocalSweepFT

/-- Claim 4.28, p.31 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `z` be a finite `d′`-chain of `T^d_∞` and `ξ` the
result of applying a sweep rule to it. For every vertex `v` of `∂⁻ξ` and every potential wall
`L_i` there is a vertex `u` of `∂⁻z` with `L_i(u) ≥ L_i(v)` for `i ≠ d + 1` and
`L_{d+1}(u) > L_{d+1}(v)`, and a `d′`-dimensional face `f` containing both `u` and `v`.

**Formalization Note.** `u` and `f` may depend on `i` (the proof picks them per wall). The rule is
any sweep rule. "Finite" is read as finitely supported. Standing assumption `d′, d − d′ ≥ 2`
(p.4). -/
theorem claim_4_28 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') (rule : LocalRule d d')
    (hrule : IsSweepRule ℤ rule) (z : Chain ℤ d d') :
    let ξ := z + sweepStep rule (bdry z)
    ∀ v ∈ chainVerts (bdry ξ), ∀ i : Fin (d + 1), ∃ u ∈ chainVerts (bdry z),
      ∃ f : Cell ℤ d d', v ∈ cellVerts f ∧ u ∈ cellVerts f ∧
        (if i = Fin.last d then pot i v < pot i u else pot i v ≤ pot i u) := by sorry

end LocalSweepFT
