-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_spectral_representation
-- name    : LeeYangGap.SpectralGap.spectral_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:39.596964+00:00
-- url     : https://prove2.me/theorems/4e5913b0-5f5d-4e91-8b03-a3e9a7df54ea
-- title:
--   Lemma 12 — Spectral representation
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, with all five real bond coefficients satisfying Definition 1, and let $H_h=H-h\sum_iZ_i$ for $h>0$. Let $\beta>0$, $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. Let $A$ be any Hermitian operator and $\widehat A=A-\langle A\rangle_\beta I$. In the complete orthonormal eigenbasis of $H_h$, with eigenvalues $E_l$ counted with multiplicity and $Z=\operatorname{Tr}e^{-\beta H_h}$,
--   $$\langle A(0)A(\beta/2)\rangle_\beta-\langle A\rangle_\beta^2=\frac1Z\sum_{l,l'}e^{-\beta(E_l+E_{l'})/2}|\langle l|\widehat A|l'\rangle|^2\ge0.$$
--   This identity controls the connected midpoint correlator for every Hermitian observable. The sum uses actual spectral data without a bottom-eigenvalue strictness assumption.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: spectral sum over sorted eigenstate labels with positive real partition function → sum over the complete actual orthonormal eigenbasis in arbitrary index order, dividing by the real part of the computed partition trace; reason: reindexing the full finite sum does not change it, and the Hermitian Hamiltonian has positive real partition trace
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 12, printed/PDF p. 12

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem spectral_representation {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) (β : ℝ) (hβ : 0 < β) (A : QOp n) (hA : A.IsHermitian) :
    twoPoint (fieldHamiltonian B h) A A β (β/2) - (mean (fieldHamiltonian B h) A β)^2 =
      (midpointSpectralSum (fieldHamiltonian B h) A β : ℂ) ∧
    0 ≤ midpointSpectralSum (fieldHamiltonian B h) A β := by sorry
end LeeYangGap.SpectralGap
