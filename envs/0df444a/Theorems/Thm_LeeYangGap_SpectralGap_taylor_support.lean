-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_taylor_support
-- name    : LeeYangGap.SpectralGap.taylor_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:41.225683+00:00
-- url     : https://prove2.me/theorems/1f822064-f6d7-4d09-bce1-87087cc36fa9
-- title:
--   Lemma 6 — Support of the Taylor coefficients
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, $\beta>0$, $M\ge1$, $\epsilon=\beta/M$ and $0\le k<M$. Write the Taylor expansion at zero of the normalized analytic logarithm as $\Phi(y)=\sum_q a_qy^q$, with $q:[n]\times\mathbb Z_M\to\mathbb N$, $\operatorname{supp}(q)=\{l:q_l\ge1\}$ and $|q|=\sum_lq_l$. If $a_q\ne0$ and its support meets both layer zero and layer $k$, then
--   $$|q|\ge\min(k,M-k)+1.$$
--   The coefficients are computed from the actual partition polynomial; the formalization uses the finite coefficient formula for $\log(P(0)(1+R))$ at each degree. This is the source's restriction on all nonzero Taylor coefficients, including the coincident-layer case $k=0$ and the single-layer case $M=1$.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: analytic log of the partition polynomial with real center logarithm → radial integral of the logarithmic derivative normalized by the real center value; reason: on the source zero-free polydisc the integrand is continuous and this equals the unique normalized holomorphic logarithm
--   - encoding: Taylor coefficients a_q of log Zε → coefficient of the formal logarithm truncated at total degree |q|; reason: Zε(0) is positive and its normalized nonconstant part has zero constant term, so higher powers cannot contribute
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 6, printed/PDF p. 8

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem taylor_support {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (β : ℝ) (hβ : 0 < β) (M : ℕ) (hM : 1 ≤ M) (k : ℕ) (hkM : k < M)
    (q : Location n M → ℕ) (ha : logCoefficient B β M q ≠ 0)
    (h0 : ∃ i : Fin n, ∃ m : Fin M, m.val = 0 ∧ 1 ≤ q (i,m))
    (hkq : ∃ i : Fin n, ∃ m : Fin M, m.val = k ∧ 1 ≤ q (i,m)) :
    layerDistance M k ≤ ∑ l, q l := by sorry
end LeeYangGap.SpectralGap
