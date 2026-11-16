-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantum_dhx
-- name    : FourWayStream.ARHM.Supplement.quantum_dhx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:14:34.655091+00:00
-- url     : https://prove2.me/theorems/5a426a1b-2354-45e7-9db9-4015bb026115
-- title:
--   Theorem D.5 — quantum Distributional Hidden XOR needs $\Omega(wt)$ qubits for $t\ge512\log w$
-- statement:
--   For sufficiently large $w$ and every $t\ge512\log_2w$, every one-way quantum protocol for $\mathrm{DHX}_{w,t}$ with success at least $\tfrac12+\tfrac1{6w}$ communicates
--   $$\Omega(wt)$$
--   qubits: there are universal $c>0$ and $w_0$ such that $q\ge c\,wt$ whenever $w\ge w_0$.
--
--   This is the quantum version of the lower bound of Assadi and Sundaresan for the intermediate problem, with the full $wt$ dependence.
--
--   **Formalization Note** The proof (Lemma D.4 and Theorem 7.10, with $r\ge t/512$ and $w'\ge w/125$) yields $c=1/(512\cdot125\cdot64)$ once $w_0$ is large enough; the statement asserts only some universal $c>0$.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: for sufficiently large w … Ω(wt) qubits → ∃ c > 0 and w₀ (universal) with c·w·t ≤ q for all w ≥ w₀, t ≥ 512 log₂ w; reason: the standard meaning of Ω/O with the constant and threshold quantified before every varying parameter, as §4 uses them
--   - encoding: each edge assigned to Alice or Bob independently with probability 1/2 → a uniform ownership function on the pairs (layer step ℓ, endpoint in layer ℓ + 1); reason: a bijection with the edges of the multi-block graph; same distribution
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.49, Theorem D.5

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem D.5 (Quantum Distributional Hidden XOR), p.49. There are `c > 0` and `w₀` such that for
every `w ≥ w₀` and every `t ≥ 512 log₂ w`, every one-way quantum protocol for `DHX_{w,t}` (message
dimension at most `2^q`) with success at least `1/2 + 1/(6w)` has `q ≥ c w t`, i.e. communicates
`Ω(wt)` qubits. -/
theorem quantum_dhx :
    ∃ c : ℝ, 0 < c ∧ ∃ w₀ : ℕ, ∀ w t : ℕ, w₀ ≤ w → 512 * Real.logb 2 w ≤ t →
      ∀ [NeZero w] {nR : ℕ} (P : ShareProtocol (DHXV w t) nR), P.Valid →
        1 / 2 + 1 / (6 * (w : ℝ)) ≤ dhxSucc P → ∀ q : ℕ, P.d ≤ 2 ^ q →
          c * w * t ≤ q := by sorry

end FourWayStream.ARHM.Supplement
