-- Prove2me | Theorems.Thm_LosslessQLTC_theorem_3_1
-- name    : LosslessQLTC.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:10:01.691308+00:00
-- url     : https://prove2.me/theorems/5cddb214-a77f-42cf-9d33-9abfbb2e53cb
-- title:
--   Theorem 3.1, p.21 — coboundary expansion of complete multipartite complexes
-- statement:
--   Let $M=K(D_1,\dots,D_d)$ be the complete $d$-partite complex with block sizes $D_1,\dots,D_d$. For $-1\le r\le d-2$, every $f\in C^r(M)$ satisfies
--
--   $$\|\delta_rf\|\ge m_{d,r}\operatorname{dist}(f),$$
--
--   with $m_{d,r}$ the constant (3.1). The source cites this result from Lubotzky, Meshulam and Mozes and gives no proof of it. It is the expansion of the reference complex that links inherit.
--
--   Differences from the source:
--   - encoding: faces of $K(D_1,\dots,D_d)$ as vertex sets, level $r\ge-1$ → partial choice functions on parts $\sigma_i$ with $D_i=|\sigma_i|$, level index $j=r+1$; reason: same instances; avoids natural-number subtraction
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Theorem 3.1, p.21, citing [LMM16, Corollary 3.1]; eq. (3.1), p.20

import Mathlib
import Definitions.Def_LosslessQLTC_Multipartite
import Definitions.Def_LosslessQLTC_mConst

namespace LosslessQLTC

/-- Theorem 3.1 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.21, citing Lubotzky, Meshulam,
Mozes 2016, Corollary 3.1): for `M = K(D_1, …, D_d)` and `−1 ≤ r ≤ d − 2`, every `f ∈ C^r(M)`
satisfies `∥δ_r f∥ ≥ m_{d,r} dist(f)`, with `m_{d,r}` as in (3.1).

**Formalization Note.** `j = r + 1`, so `−1 ≤ r ≤ d − 2` is `j < d`. The parts are nonempty types
`σ i` with `D_i = |σ i|`. -/
theorem theorem_3_1 {d : ℕ} (σ : Fin d → Type) [∀ i, Fintype (σ i)] [∀ i, DecidableEq (σ i)]
    [∀ i, Nonempty (σ i)] (j : ℕ) (hj : j < d) (f : MLevel σ j → ZMod 2) :
    mConst d j * mDist σ j f ≤ mNorm σ (mDelta σ j f) := by sorry

end LosslessQLTC
