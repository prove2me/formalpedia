-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_6
-- name    : LocalSweepFT.claim_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:47.847384+00:00
-- url     : https://prove2.me/theorems/b707de96-7356-4fb0-b6b6-3a8c1cefa654
-- title:
--   Claim 5.6 — small boundary components have small fillings
-- statement:
--   Let $d'\ge2$, $d-d'\ge2$, $n\ge1$, and let $x$ be a $d'$-chain of $\mathcal T^d_n$. Suppose that for some integer $l\le n-1$ every connected component of $\partial^-x$ has size less than $l$. Then every connected component $\kappa$ of $\partial^-x$ is the boundary of a $d'$-chain $y$ with
--   $$\partial^-y=\kappa,\qquad\mathrm{Size}(y)\le\mathrm{Size}(\partial^-y).$$
--
--   These fillings define the filling operator $[x]$ of Def. 5.7, the logical class read off a chain with small syndrome clusters.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - encoding: chains y₁, y₂, … such that each ∂⁻y_i is a connected component of ∂⁻x → for every component κ there is y with ∂⁻y = κ; reason: one filling per component, as constructed in the proof
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.6, p.41

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT

namespace LocalSweepFT

/-- Claim 5.6, p.41 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `x ∈ C_{d′}(T^d_n)`. Suppose there is an integer
`l ≤ n − 1` such that each connected component of `∂⁻x` has size `< l`. Then every connected
component `κ` of `∂⁻x` is the boundary `∂⁻y` of a `d′`-chain `y` with `Size(y) ≤ Size(∂⁻y)`.

**Formalization Note.** One filling `y` per component (the chains `y_1, y_2, …` of the claim).
Standing assumption `d′, d − d′ ≥ 2` (p.4); the proof uses `d′ ≥ 2`. Sizes are torus sizes
(Def 5.1). -/
theorem claim_5_6 (d d' n : ℕ) [NeZero n] (h1 : 2 ≤ d') (h2 : 2 ≤ d - d')
    (x : Chain (ZMod n) d d') (l : ℤ) (hl : l ≤ (n : ℤ) - 1)
    (hsize : ∀ κ ∈ components (bdry x), sizeT n κ < l) :
    ∀ κ ∈ components (bdry x), ∃ y : Chain (ZMod n) d d', bdry y = κ ∧ sizeT n y ≤ sizeT n κ := by sorry

end LocalSweepFT
