-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_robust_ngc_to_bhx
-- name    : FourWayStream.ARHM.Supplement.robust_ngc_to_bhx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:06:25.779611+00:00
-- url     : https://prove2.me/theorems/ad45744a-0b0e-4aa2-a2e0-9804515fac30
-- title:
--   Lemma 7.6 — from robust $\mathrm{NGC}_{n,k}$ to $\mathrm{BHX}_{\lfloor w/100\rfloor,r}$, $r\ge t/512$, advantage $1/(8w)$
-- statement:
--   Let $t,m$ be positive integers, $k=3t+1$, $n=4km$ and $w=m+1$, and suppose that $t\ge512\log_2w$ and that $w$ is large enough (at least a universal threshold $w_0$). A $q$-qubit robust one-way protocol for $\mathrm{NGC}_{n,k}$ with error at most $1/3$ gives a $q$-qubit protocol for $\mathrm{BHX}_{w',r}$ with
--   $$w'=\lfloor w/100\rfloor,\qquad r\ge t/512,\qquad\text{success at least }\frac12+\frac1{8w}.$$
--
--   The small advantage $1/(8w)$ is the price of the reductions; it is why the Block Hidden XOR bound (Theorem 7.10) must hold for small advantage.
--
--   **Formalization Note** "Gives a protocol" is the existence of a valid $\mathrm{BHX}_{w',r}$ protocol whose message dimension is at most $2^q$, for some integer $r\ge t/512$.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: w large enough → w ≥ w₀ for a universal threshold w₀ quantified before t, m and the protocol; reason: the meaning of “large enough” in the proof (p.48: arithmetic thresholds independent of t)
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.35, Lemma 7.6 (proof Appendix D, pp.46–49)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma 7.6 (From robust NGC to Block Hidden XOR), p.35. There is a width threshold `w₀` such
that: let `t, m` be positive integers, `k = 3t + 1`, `n = 4km`, `w = m + 1 ≥ w₀`, and
`t ≥ 512 log₂ w`. A `q`-qubit robust one-way protocol for `NGC_{n,k}` with error at most `1/3` gives
a `q`-qubit protocol for `BHX_{w′,r}` with `w′ = ⌊w/100⌋`, `r ≥ t/512` and success at least
`1/2 + 1/(8w)`. -/
theorem robust_ngc_to_bhx :
    ∃ w₀ : ℕ, ∀ t m : ℕ, 1 ≤ t → 1 ≤ m → w₀ ≤ m + 1 →
      512 * Real.logb 2 ((m + 1 : ℕ) : ℝ) ≤ t →
      ∀ {nR : ℕ} (P : ShareProtocol (Fin (4 * (3 * t + 1) * m)) nR), P.Valid →
        RobustNGCErrorLE P (3 * t + 1) (1 / 3) → ∀ q : ℕ, P.d ≤ 2 ^ q →
        ∃ r : ℕ, (t : ℝ) / 512 ≤ r ∧ ∃ (nR' : ℕ) (P' : BHXProtocol ((m + 1) / 100) r nR'),
          P'.Valid ∧ P'.d ≤ 2 ^ q ∧ 1 / 2 + 1 / (8 * ((m + 1 : ℕ) : ℝ)) ≤ P'.succ := by sorry

end FourWayStream.ARHM.Supplement
