-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_partition_zero_free
-- name    : LeeYangGap.SpectralGap.partition_zero_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:15.275824+00:00
-- url     : https://prove2.me/theorems/846edbbb-ab7f-4aac-b52e-a523912e2fdc
-- title:
--   Lemma 2 — Zero-freeness of the full Trotter partition polynomial
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, let $\beta>0$, $M\ge1$ be an integer and $\epsilon=\beta/M$. Put $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$ in the fixed bond order. For every independent complex assignment $y=(y_{i,m})$ with $|y_{i,m}|<1$,
--   $$\mathcal Z_\epsilon(y)=\operatorname{Tr}\prod_{m\in\mathbb Z_M}LD_m(y)L^\dagger=\sum_{x_0,\ldots,x_{M-1}}\prod_m(L^\dagger L)_{x_m,x_{m+1}}\prod_i y_{i,m}^{(x_m)_i}\ne0,$$
--   where $D_m(y)=\prod_i(|0\rangle\langle0|_i+y_{i,m}|1\rangle\langle1|_i)$ and $x_M=x_0$. Zero-freeness is asserted for the actual trace polynomial and all intermediate-layer variables, not included in admissibility as a hypothesis. This is the source's attributed Suzuki–Fisher input.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 2, printed/PDF p. 5

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem partition_zero_free {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (β : ℝ) (hβ : 0 < β) (M : ℕ) (hM : 1 ≤ M)
    (y : LayerVariables n M) (hy : ∀ l, ‖y l‖ < 1) :
    trotterPartition B β M y = MvPolynomial.eval y (partitionPolynomial B β M) ∧
    trotterPartition B β M y ≠ 0 := by sorry
end LeeYangGap.SpectralGap
