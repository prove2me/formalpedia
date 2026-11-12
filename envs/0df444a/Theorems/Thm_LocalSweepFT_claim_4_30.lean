-- Prove2me | Theorems.Thm_LocalSweepFT_claim_4_30
-- name    : LocalSweepFT.claim_4_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:42:59.723202+00:00
-- url     : https://prove2.me/theorems/d18df6b3-95e0-4a79-9b7b-fa40179e0062
-- title:
--   Claim 4.30 — $x_{S'}$ and $z_{S'}$ are anticommuting logical operators of the $(d,d')$-Toric code
-- statement:
--   Let $1\le d'<d$, $n\ge1$, and let $S'$ be a set of $d'$ generators. On the side-$n$ $(d,d')$-Toric code,
--   1. $\partial^-x_{S'}=0$ and $\partial^+z_{S'}=0$, so $x_{S'}\in C_X$ and $z_{S'}\in C_Z$;
--   2. $\langle x_{S'},z_{S'}\rangle=1$;
--   3. $x_{S'}\notin C_Z^\perp=\operatorname{im}\partial^-$ and $z_{S'}\notin C_X^\perp=\operatorname{im}\partial^+$;
--   4. the Pauli operators $X_{S'}=X^{x_{S'}}$ and $Z_{S'}=Z^{z_{S'}}$ anticommute.
--
--   These are the logical operators used by every logical gate of the construction and by the nice encoding.
--
--   Differences from the source:
--   - encoding: x_{S′} ∈ C_X/C_Z^⊥ and z_{S′} ∈ C_Z/C_X^⊥ (non-trivial logical classes) → x_{S′} ∈ ker ∂⁻, x_{S′} ∉ im ∂⁻; z_{S′} ∈ ker ∂⁺, z_{S′} ∉ im ∂⁺ (via Chain.recast); reason: membership in the quotient as a non-zero class
--   - encoding: the code of Def 4.3 → 1 ≤ d′ < d and every side length n ≥ 1; reason: Def 4.3's range of d′
--   - encoding: "binary representations of anticommuting logical codewords" → ⟨x_{S′}, z_{S′}⟩ = 1 and X^{x}Z^{z} = −Z^{z}X^{x}; reason: the inner product is the paper's "In particular"; the matrix identity is the anticommutation
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 4.30, p.32

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_xLog
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat

namespace LocalSweepFT

/-- Claim 4.30, p.32 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). For every direction set `S′` of size `d′`
(`1 ≤ d′ < d`, Def 4.3), `x_{S′}` and `z_{S′}` represent anticommuting logical operators of the
side-`n` `(d, d′)`-Toric code: `x_{S′} ∈ C_X = ker ∂⁻`, `z_{S′} ∈ C_Z = ker ∂⁺`,
`⟨x_{S′}, z_{S′}⟩ = 1`, `x_{S′} ∉ C_Z^⊥ = im ∂⁻`, `z_{S′} ∉ C_X^⊥ = im ∂⁺`, and the Paulis
`X_{S′}`, `Z_{S′}` anticommute.

**Formalization Note.** "`x_{S′} ∈ C_X/C_Z^⊥`" is read as "in `C_X` and not in `C_Z^⊥`" (a
non-trivial logical). The image of `∂⁺ : C_{d′−1} → C_{d′}` is written through `Chain.recast`, since
`d′ − 1 + 1 = d′` holds only for `d′ ≥ 1`. -/
theorem claim_4_30 (d d' n : ℕ) [NeZero n] (h1 : 1 ≤ d') (h2 : d' < d) (S : DirSet d d') :
    bdry (xLog (n := n) S) = 0 ∧
    cobdry (zLog (n := n) S) = 0 ∧
    inner (xLog (n := n) S) (zLog S) = 1 ∧
    xLog (n := n) S ∉ bdryRange (ZMod n) d d' ∧
    (∀ y : Chain (ZMod n) d (d' - 1), Chain.recast (by omega) (cobdry y) ≠ zLog (n := n) S) ∧
    xOn ⇑(xLog (n := n) S) * zOn ⇑(zLog (n := n) S) =
      -(zOn ⇑(zLog (n := n) S) * xOn ⇑(xLog (n := n) S)) := by sorry

end LocalSweepFT
