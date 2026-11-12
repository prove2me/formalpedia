-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_8
-- name    : LocalSweepFT.claim_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:43.509244+00:00
-- url     : https://prove2.me/theorems/eec6a443-b840-4994-bac5-ca6df8825bf5
-- title:
--   Claim 5.8 (corrected: $l\ge1$) — boundary components grow by at most $4\binom{d'}{2}l(r+d')$ under $l$ flips
-- statement:
--   Let $d'\ge2$, $d-d'\ge2$, $n\ge1$, and let $x_1,x_2$ be $d'$-chains of $\mathcal T^d_n$ at Hamming distance at most $l$, where $l\ge1$. If every connected component of $\partial^-x_1$ has size at most $r$, then every connected component of $\partial^-x_2$ has size at most
--   $$4\binom{d'}{2}\,l\,(r+d').$$
--
--   It controls how fast syndrome clusters can merge when a few qubits change, and gives the constant of Claim 5.10.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - correction: l any integer with the Hamming distance at most l (l = 0 allowed, bound 4·C(d′,2)·0·(r + d′) = 0) → 1 ≤ l; reason: counterexample: n ≥ 2, x₁ = x₂ = a single d′-cell θ_{v,S′}; the Hamming distance is 0 ≤ l = 0, and ∂⁻x₂ is one connected component (its (d′−1)-faces meet pairwise through (d′−2)-faces) of size d′ > 0; the claim is used only with l = ∆ ≥ 1
--   - reading: r is the size of the maximal connected component of ∂⁻x₁ → r is any bound on the sizes of the components of ∂⁻x₁; reason: equivalent, since the bound is monotone in r; it also covers ∂⁻x₁ = 0
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.8, p.42

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT

namespace LocalSweepFT

/-- Claim 5.8, p.42 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)), corrected to `l ≥ 1`. Let `x₁, x₂ ∈ C_{d′}(T^d_n)` be at
Hamming distance at most `l`, and let `r` bound the size of every connected component of `∂⁻x₁`.
Then every connected component of `∂⁻x₂` has size at most `4·C(d′,2)·l·(r + d′)`.

**Formalization Note.** The printed claim allows `l = 0`, where the bound is `0`; but `x₁ = x₂ =` one
`d′`-cell (`n ≥ 2`) has a boundary that is one connected component of positive size. The statement
therefore requires `l ≥ 1` (the claim is used with `l = ∆ ≥ 1`, Claim 5.10). `r` is any bound on
the component sizes of `∂⁻x₁` (equivalent to the maximal size, since the bound is monotone in `r`).
Standing assumption `d′, d − d′ ≥ 2` (p.4). -/
theorem claim_5_8 (d d' n : ℕ) [NeZero n] (h1 : 2 ≤ d') (h2 : 2 ≤ d - d')
    (x₁ x₂ : Chain (ZMod n) d d') (l : ℕ) (hl : 1 ≤ l) (hdist : hamming x₁ x₂ ≤ l) (r : ℕ)
    (hr : ∀ κ ∈ components (bdry x₁), sizeT n κ ≤ r) :
    ∀ κ ∈ components (bdry x₂), sizeT n κ ≤ 4 * (d'.choose 2 : ℤ) * l * (r + d') := by sorry

end LocalSweepFT
