-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_5
-- name    : LocalSweepFT.claim_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:48.30197+00:00
-- url     : https://prove2.me/theorems/92e68959-3cec-49bd-a568-bf4ed19d55f6
-- title:
--   Claim 5.5 — a chain closing a non-trivial loop on the torus has size $\ge n-1$
-- statement:
--   Let $n\ge1$, $i\ge1$, and let $x$ be an $i$-chain of the torus $\mathcal T^d_n$ that closes a non-trivial loop: $\partial^-x=0$ and $x\notin\operatorname{im}\partial^-$. Then
--   $$\mathrm{Size}(x)\ge n-1.$$
--
--   Small cycles are therefore stabilizers; this is what makes the filling class of a chain with small syndrome clusters well defined.
--
--   Differences from the source:
--   - reading: "closes a non-trivial loop" → a non-bounding cycle: ∂⁻x = 0 and x ∉ im ∂⁻; reason: the homological meaning used in Claim 5.6 ("a non-trivial codeword … has to close a non-trivial loop")
--   - reading: x ∈ C_i for any i → i ≥ 1; reason: a 0-chain closes no loop: a single vertex is a non-bounding 0-cycle of size 0 < n − 1; the claim is used at i = d′ − 1 ≥ 1 (Claim 5.6)
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.5, p.40

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT

namespace LocalSweepFT

/-- Claim 5.5, p.40 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). If an `i`-chain `x` on the torus `T^d_n` closes a
non-trivial loop, then `Size(x) ≥ n − 1`.

**Formalization Note.** "Closes a non-trivial loop" is read as a non-bounding cycle: `∂⁻x = 0` and
`x ∉ im ∂⁻`. The dimension is `i ≥ 1`: a `0`-chain closes no loop (a single vertex is a non-bounding
`0`-cycle of size `0`). `Size` is the torus size of Def 5.1. -/
theorem claim_5_5 (d n i : ℕ) [NeZero n] (hi : 1 ≤ i) (x : Chain (ZMod n) d i)
    (hcyc : bdry x = 0) (hnt : x ∉ bdryRange (ZMod n) d i) :
    (n : ℤ) - 1 ≤ sizeT n x := by sorry

end LocalSweepFT
