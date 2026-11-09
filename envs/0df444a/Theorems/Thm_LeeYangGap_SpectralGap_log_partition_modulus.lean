-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_log_partition_modulus
-- name    : LeeYangGap.SpectralGap.log_partition_modulus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:49.512016+00:00
-- url     : https://prove2.me/theorems/b3f87bc7-10cf-47f9-8488-d99dcd69359a
-- title:
--   Lemma 7 — Modulus bound on the log-partition function
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. Let $M\ge1$ and $\epsilon=\beta/M$, and suppose $\epsilon h\le2$. For $C_\star=\max(n,6\beta W)$ and the normalized analytic logarithm $\Phi$ of $\mathcal Z_\epsilon$, every point with $|y_l|\le e^{-\epsilon h/2}$ for all site-layer locations $l$ satisfies
--   $$|\Phi(y)|\le\frac{16C_\star}{\epsilon h}.$$
--   The universal pointwise form is equivalent to the source's supremum bound and includes the boundary of this closed inner polydisc.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: analytic log of the partition polynomial with real center logarithm → radial integral of the logarithmic derivative normalized by the real center value; reason: on the source zero-free polydisc the integrand is continuous and this equals the unique normalized holomorphic logarithm
--   - encoding: supremum bound over a closed polydisc → the same bound at every point of the closed polydisc; reason: equivalent bound without default values of real suprema
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 7, printed/PDF p. 8

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem log_partition_modulus {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (M : ℕ) (hM : 1 ≤ M)
    (hε : stepSize β M * h ≤ 2) (y : LayerVariables n M)
    (hy : ∀ l, ‖y l‖ ≤ Real.exp (-stepSize β M * h / 2)) :
    ‖logPartition B β M y‖ ≤ 16 * cStar B β / (stepSize β M * h) := by sorry
end LeeYangGap.SpectralGap
