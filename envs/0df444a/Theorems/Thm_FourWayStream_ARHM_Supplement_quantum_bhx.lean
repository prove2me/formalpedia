-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantum_bhx
-- name    : FourWayStream.ARHM.Supplement.quantum_bhx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:09:15.751903+00:00
-- url     : https://prove2.me/theorems/02e984c9-d998-40fe-aea4-34affc15e783
-- title:
--   Theorem 7.9 — quantum Block Hidden XOR: $q\ge\frac r{2\lambda}\log(A\lambda)$, and $q\ge rA/4$ if $A=w(2\gamma)^{2/r}\ge2$
-- statement:
--   Let $w$ and $r$ be positive integers and $0\le\gamma\le1/2$. Suppose a one-way protocol in which Alice sends a state of dimension at most $2^q$ succeeds with probability at least $\tfrac12+\gamma$ on $\mathrm{BHX}_{w,r}$, averaged over the input distribution of Definition 7.5 and all protocol randomness. Let
--   $$A=w\,(2\gamma)^{2/r},$$
--   the width discounted by the advantage. Then for every $0<\lambda\le1$ with $A\lambda>1$,
--   $$q\ge\frac r{2\lambda}\log_2(A\lambda),$$
--   and in particular, if $A\ge2$, then $q\ge rA/4=\frac{rw}4(2\gamma)^{2/r}$.
--
--   The advantage enters only through $(2\gamma)^{2/r}$, so even a small advantage forces $\Omega(wr)$ qubits once $r\ge\log w$ (Theorem 7.10).
--
--   **Formalization Note** $2/r$ is real division and $\lambda$ is written `lam`. For $\gamma=0$, $A=0$ and both premises are false, so nothing is claimed, as in the paper.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.36, Theorem 7.9

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.9 (Quantum Block Hidden XOR), p.36. Let `w, r` be positive integers and
`0 ≤ γ ≤ 1/2`. Suppose a one-way protocol in which Alice sends a state of dimension at most `2^q`
succeeds with probability at least `1/2 + γ` on `BHX_{w,r}`, averaged over the input distribution of
Definition 7.5 and all protocol randomness. Let `A = w (2γ)^{2/r}`. For every `0 < λ ≤ 1` with
`Aλ > 1`, `q ≥ (r/(2λ)) log₂(Aλ)`. In particular, if `A ≥ 2`, then `q ≥ rA/4 = (rw/4)(2γ)^{2/r}`. -/
theorem quantum_bhx (w r : ℕ) (hw : 1 ≤ w) (hr : 1 ≤ r) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1 / 2)
    {nR : ℕ} (P : BHXProtocol w r nR) (hP : P.Valid) (q : ℕ) (hq : P.d ≤ 2 ^ q)
    (hsucc : 1 / 2 + γ ≤ P.succ) :
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 → 1 < (w : ℝ) * (2 * γ) ^ ((2 : ℝ) / r) * lam →
      (r : ℝ) / (2 * lam) * Real.logb 2 ((w : ℝ) * (2 * γ) ^ ((2 : ℝ) / r) * lam) ≤ q) ∧
    (2 ≤ (w : ℝ) * (2 * γ) ^ ((2 : ℝ) / r) →
      (r : ℝ) * ((w : ℝ) * (2 * γ) ^ ((2 : ℝ) / r)) / 4 ≤ q) := by sorry

end FourWayStream.ARHM.Supplement
