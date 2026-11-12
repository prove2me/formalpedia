-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_27
-- name    : LocalSweepFT.claim_4_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:00.871561+00:00
-- url     : https://prove2.me/theorems/5efa374a-398d-417a-aef4-229d4164fb51
-- title:
--   Claim 4.27 — the sweep rule lowers every potential wall of the syndrome and $L_{d+1}$ strictly
-- statement:
--   Let $d'\ge2$, $d-d'\ge2$, let $\mathrm{rule}$ be any sweep rule on the infinite cover $\mathcal T^d_\infty$, $z$ a finitely supported $d'$-chain, and $\xi=z+\sum_v\varphi_v$ the chain after one parallel application of the rule to the syndrome $\partial^-z$. Then
--   1. for every generator $g$: $\max\{L_g(v):v\in\partial^-z\}\ge\max\{L_g(v):v\in\partial^-\xi\}$;
--   2. $\max\{L_{d+1}(v):v\in\partial^-z\}\ge\max\{L_{d+1}(v):v\in\partial^-\xi\}+1$;
--   3. in particular, if $\partial^-z\ne0$, then $\mathrm{Size}(\partial^-\xi)\le\mathrm{Size}(\partial^-z)-1$.
--
--   The sweep rule shrinks every finite error cluster; this is the local mechanism behind both the threshold theorem and the decoder of §7.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - generalization: z a finite chain (Def 4.22: Size(z) ≤ n − 1) → every finitely supported d′-chain of ℤ^d; reason: finite chains in the sense of Def 4.22 are a special case
--   - reading: "the sweep rule" → every sweep rule (IsSweepRule ℤ); reason: the proof uses only the sweep-rule conditions; Def 4.6 does not fix which admissible chain is flipped
--   - encoding: max{…} ≥ max{…} (+1) → every vertex of ∂⁻ξ is dominated (strictly by at least 1 for L_{d+1}) by a vertex of ∂⁻z; reason: equivalent when ∂⁻ξ ≠ 0, and avoids the maximum over the empty set
--   - reading: in particular Size(∂⁻ξ) ≤ Size(∂⁻z) − 1 → the same, when ∂⁻z ≠ 0; reason: for ∂⁻z = 0 nothing is flipped and Size(∅) = 0
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.27, p.30

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT
import Definitions.Def_LocalSweepFT_IsSweepRule

namespace LocalSweepFT

/-- Claim 4.27, p.30 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `z` be a finite `d′`-chain of `T^d_∞` and
`ξ = z + Σ_v φ_v` the result of applying a sweep rule at every vertex. Then
1. for every generator `g`: `max{L_g(v) : v ∈ ∂⁻z} ≥ max{L_g(v) : v ∈ ∂⁻ξ}`;
2. `max{L_{d+1}(v) : v ∈ ∂⁻z} ≥ max{L_{d+1}(v) : v ∈ ∂⁻ξ} + 1`;
in particular `Size(∂⁻ξ) ≤ Size(∂⁻z) − 1`.

**Formalization Note.** The maxima are compared vertex by vertex ("every vertex of `∂⁻ξ` is
dominated by some vertex of `∂⁻z`"), which avoids a maximum over the empty set; the "in particular"
is stated for `∂⁻z ≠ 0` (for `∂⁻z = 0` nothing is flipped). The rule is any sweep rule
(`IsSweepRule ℤ`). "Finite" is read as finitely supported. Standing assumption `d′, d − d′ ≥ 2`
(p.4). -/
theorem claim_4_27 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') (rule : LocalRule d d')
    (hrule : IsSweepRule ℤ rule) (z : Chain ℤ d d') :
    let ξ := z + sweepStep rule (bdry z)
    (∀ j : Fin d, ∀ u ∈ chainVerts (bdry ξ), ∃ w ∈ chainVerts (bdry z),
      pot j.castSucc u ≤ pot j.castSucc w) ∧
    (∀ u ∈ chainVerts (bdry ξ), ∃ w ∈ chainVerts (bdry z),
      pot (Fin.last d) u + 1 ≤ pot (Fin.last d) w) ∧
    (bdry z ≠ 0 → sizeZ (bdry ξ) ≤ sizeZ (bdry z) - 1) := by sorry

end LocalSweepFT
