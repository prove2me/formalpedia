-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_4
-- name    : LocalSweepFT.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:51.552926+00:00
-- url     : https://prove2.me/theorems/cecabf1b-d429-4aaa-a9ff-9f6473302e17
-- title:
--   Claim 4.4 — the $(d,d')$-Toric code is a CSS code ($\partial^-\partial^-=0$, $\partial^+$ is the transpose of $\partial^-$)
-- statement:
--   For every commutative coefficient ring $R$ of vertex coordinates (the torus $\mathbb Z_n$ or the infinite cover $\mathbb Z$) and every dimension $i$,
--   1. $\partial^-\partial^-x=0$ and $\partial^+\partial^+x=0$ for every chain $x$;
--   2. $\langle\partial^+x,y\rangle=\langle x,\partial^-y\rangle$ for every $i$-chain $x$ and $(i+1)$-chain $y$;
--   3. $\operatorname{im}(\partial^-:C_{i+1}\to C_i)\subseteq\ker(\partial^-:C_i\to C_{i-1})$.
--
--   So the check matrices of adjacent dimensions are orthogonal and the X- and Z-stabilizers commute: the $(d,d')$-Toric code is a CSS code.
--
--   Differences from the source:
--   - encoding: "is a CSS code" → ∂⁻∂⁻ = 0, ∂⁺∂⁺ = 0, ⟨∂⁺x, y⟩ = ⟨x, ∂⁻y⟩ and im ∂⁻ ⊆ ker ∂⁻; reason: the content of the proof (p.18): orthogonal check matrices
--   - generalization: the side-n (d, d′)-Toric code, 1 ≤ d′ < d → every dimension i and every coefficient ring R (ZMod n and ℤ included); reason: the identities hold cellwise for every R; i = d′, R = ZMod n is the case of the claim
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.4 and its proof, p.18

import Mathlib
import Definitions.Def_LocalSweepFT_Chain

namespace LocalSweepFT

/-- Claim 4.4 (CSS structure), p.18 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). The `(d, d′)`-Toric code is a CSS
code: `∂⁻∂⁻ = 0`, `∂⁺∂⁺ = 0`, `∂⁺` is the transpose of `∂⁻` in consecutive dimensions
(`⟨∂⁺x, y⟩ = ⟨x, ∂⁻y⟩`), and hence the X-stabilizers `im ∂⁻` are X-type codewords (`⊆ ker ∂⁻`).

**Formalization Note.** Stated for every dimension `i` and every coefficient ring `R` (the torus
`ZMod n` and the infinite cover `ℤ` included); the code of Def 4.3 is the case `i = d′`,
`R = ZMod n`. -/
theorem claim_4_4 (R : Type) [CommRing R] [DecidableEq R] (d i : ℕ) :
    (∀ x : Chain R d i, bdry (bdry x) = 0) ∧
    (∀ x : Chain R d i, cobdry (cobdry x) = 0) ∧
    (∀ (x : Chain R d i) (y : Chain R d (i + 1)), inner (cobdry x) y = inner x (bdry y)) ∧
    bdryRange R d i ≤ LinearMap.ker (bdry (R := R) (d := d) (i := i)) := by sorry

end LocalSweepFT
