-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_log_partition_correlator
-- name    : LeeYangGap.SpectralGap.log_partition_correlator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:52.760376+00:00
-- url     : https://prove2.me/theorems/c563d292-a604-41b9-bb95-3f9df291c79f
-- title:
--   Lemma 5 — Correlator through log-partition function
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For a nonempty $S\subseteq[n]$, put $Z_S=\prod_{i\in S}Z_i$. For an integer $M\ge2$ put $\epsilon=\beta/M$; the layer $k$ satisfies $1\le k<M$. All Trotter quantities are computed from the ordered product $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$ and the cyclic trace polynomial. Let $\Phi$ be the normalized analytic logarithm of $\mathcal Z_\epsilon$ on the unit polydisc. The constant point $y_\star$ has coordinates $e^{-2\epsilon h}$; $\sigma_m$ flips the coordinates in $S$ at layer $m$. Put
--   $$u_k=\Phi(\sigma_0\sigma_k y_\star)+\Phi(y_\star)-\Phi(\sigma_0y_\star)-\Phi(\sigma_ky_\star).$$
--   There is $A\in\mathbb C$ with $|A|\le1$ such that
--   $$f_{S,\epsilon}(k)=A(e^{u_k}-1).$$
--   Moreover $|f_{S,\epsilon}(k)|\le2$, and $|u_k|\le1$ implies $|f_{S,\epsilon}(k)|\le2|u_k|$. All three assertions connect the logarithmic combination with the physical correlator.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: analytic log of the partition polynomial with real center logarithm → radial integral of the logarithmic derivative normalized by the real center value; reason: on the source zero-free polydisc the integrand is continuous and this equals the unique normalized holomorphic logarithm
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 5, printed/PDF p. 7

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem log_partition_correlator {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : 1 ≤ k) (hkM : k < M) :
    (∃ A : ℂ, ‖A‖ ≤ 1 ∧ trotterConnected B h β M S k =
      A * (Complex.exp (logCombination B h β M S k) - 1)) ∧
    ‖trotterConnected B h β M S k‖ ≤ 2 ∧
    (‖logCombination B h β M S k‖ ≤ 1 →
      ‖trotterConnected B h β M S k‖ ≤ 2 * ‖logCombination B h β M S k‖) := by sorry
end LeeYangGap.SpectralGap
