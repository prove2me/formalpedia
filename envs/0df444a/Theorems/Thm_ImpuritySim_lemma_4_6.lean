-- Prove2me | Theorems.Thm_ImpuritySim_lemma_4_6
-- name    : ImpuritySim.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:19.920932+00:00
-- url     : https://prove2.me/theorems/4bba7b32-4e3d-4f5e-a7b4-0cb14b4e02e6
-- title:
--   Lemma 4.6 — $\sum_{I\sim q}e^{2\lambda h(I)}\mathrm{Re\,Tr}(\rho A_I^\dagger B_I)\ge\bigl(\frac12\sum_\ell q_\ell\omega_\ell\bigr)F_q$
-- statement:
--   Fix a nonzero $q=(q_0,\dots,q_L)$. For a state $\rho$, a Hamiltonian in the form (3.15), $\lambda=1/4$ and weights satisfying (4.2),
--   $$\sum_{I\sim q}e^{2\lambda h(I)}\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger B_I)\ \ge\ \Bigl(\frac12\sum_\ell q_\ell\omega_\ell\Bigr)F_q.\qquad(4.26)$$
--
--   The bath-replacement term of the commutator identity is therefore a positive multiple of the joint occupation $F_q$.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 4.6, Eq. (4.26), p.24

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Lemma 4.6 (Lower bound on the bath term)**, p.24, of J. Jiang, N. Ju, O. Parekh, C. Rayudu,
A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (4.26).

Fix nonzero `q = (q_0, …, q_L)`. Then
`Σ_{I∼q} e^{2λh(I)} Re Tr(ρ A_I† B_I) ≥ ((1/2) Σ_ℓ q_ℓ ω_ℓ) F_q`.

**Formalization Note.** `λ = 1/4` (4.5); the weights satisfy (4.2) and `ρ` is a density matrix
(standing assumptions of §4). -/
theorem lemma_4_6 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (hh : ValidWeights h)
    (ρ : FermiCap.Gaussian.Op n) (hρ : IsDensity ρ) (q : Fin (F.L + 1) → ℕ) (hq : q ≠ 0) :
    (1 / 2 * ∑ ℓ : Fin (F.L + 1), (q ℓ : ℝ) * F.omegaL ℓ) * F.Fq h ρ q ≤
      ∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) * (ρ * (AI n I)ᴴ * F.BI I).trace.re := by sorry

end ImpuritySim
