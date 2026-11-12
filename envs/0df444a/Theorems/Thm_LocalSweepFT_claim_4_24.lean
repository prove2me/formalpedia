-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_24
-- name    : LocalSweepFT.claim_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:55.845298+00:00
-- url     : https://prove2.me/theorems/cee7a68b-44ce-4953-9467-24af85700b0b
-- title:
--   Claim 4.24 — a size-minimizing stabilizer translate has the size of its boundary
-- statement:
--   Let $d'\ge2$, $d-d'\ge2$, let $x$ be a finitely supported $d'$-chain of $\mathcal T^d_\infty$, and let $z\in C_Z^\perp=\operatorname{im}\partial^-$ minimize $\mathrm{Size}(x+z)$ over $C_Z^\perp$. Then
--   $$\mathrm{Size}(x+z)=\mathrm{Size}(\partial^-(x+z)).$$
--
--   A reduced error is no larger than its syndrome; the sweep rule acts on the syndrome, so this transfers the shrinking of Claim 4.27 to the error itself.
--
--   Differences from the source:
--   - encoding: standing assumption "Fix integers d, d′ satisfying d′, d − d′ ≥ 2" (p.4) → hypotheses 2 ≤ d′ and 2 ≤ d − d′; reason: the section's standing assumption is a hypothesis of each statement
--   - generalization: x a finite chain (Def 4.22: Size(x) ≤ n − 1) → every finitely supported d′-chain of ℤ^d; reason: finite chains in the sense of Def 4.22 are a special case
--   - reading: z = arg min_{z ∈ C_Z^⊥} Size(x + z) → every minimizer z; reason: the arg min may not be unique; every minimizer is covered
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.24, p.28

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_sizeT

namespace LocalSweepFT

/-- Claim 4.24, p.28 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `x ∈ C_{d′}(T^d_∞)` be a finite `d′`-chain and `z ∈ C_Z^⊥`
an X-stabilizer minimizing `Size(x + z)`. Then `Size(x + z) = Size(∂⁻(x + z))`.

**Formalization Note.** Every minimizer `z` is covered (the printed `arg min` is any minimizer).
"Finite" is read as finitely supported (every chain of `ℤ^d` here). Standing assumption
`d′, d − d′ ≥ 2` (p.4). -/
theorem claim_4_24 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') (x z : Chain ℤ d d')
    (hz : z ∈ bdryRange ℤ d d')
    (hmin : ∀ z' ∈ bdryRange ℤ d d', sizeZ (x + z) ≤ sizeZ (x + z')) :
    sizeZ (x + z) = sizeZ (bdry (x + z)) := by sorry

end LocalSweepFT
