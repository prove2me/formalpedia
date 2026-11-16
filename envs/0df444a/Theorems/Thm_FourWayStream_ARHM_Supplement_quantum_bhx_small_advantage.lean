-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantum_bhx_small_advantage
-- name    : FourWayStream.ARHM.Supplement.quantum_bhx_small_advantage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:09:47.00429+00:00
-- url     : https://prove2.me/theorems/b22077ad-99ff-437b-81fd-f7451ec6ebc4
-- title:
--   Theorem 7.10 — quantum Block Hidden XOR with advantage $1/(1000w)$ needs $rw/64$ qubits
-- statement:
--   Let $w\ge2000$ and $r\ge\log_2w$ be integers. Every one-way quantum protocol for $\mathrm{BHX}_{w,r}$ with success at least $\tfrac12+\tfrac1{1000w}$ communicates at least
--   $$\frac{rw}{64}$$
--   qubits.
--
--   This is the form used for Noisy Gap Cycle, where the reductions leave an advantage of order $1/w$.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.36, Theorem 7.10 (proof p.37)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.10 (Quantum Block Hidden XOR with small advantage), p.36. Let `w ≥ 2000` and
`r ≥ log₂ w` be integers. Every one-way quantum protocol for `BHX_{w,r}` (message dimension at most
`2^q`) with success at least `1/2 + 1/(1000w)` has `q ≥ rw/64`. -/
theorem quantum_bhx_small_advantage (w r : ℕ) (hw : 2000 ≤ w) (hr : Real.logb 2 w ≤ r)
    {nR : ℕ} (P : BHXProtocol w r nR) (hP : P.Valid) (q : ℕ) (hq : P.d ≤ 2 ^ q)
    (hsucc : 1 / 2 + 1 / (1000 * (w : ℝ)) ≤ P.succ) : (r : ℝ) * w / 64 ≤ q := by sorry

end FourWayStream.ARHM.Supplement
