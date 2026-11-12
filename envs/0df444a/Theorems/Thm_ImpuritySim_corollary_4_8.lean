-- Prove2me | Theorems.Thm_ImpuritySim_corollary_4_8
-- name    : ImpuritySim.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:12.691683+00:00
-- url     : https://prove2.me/theorems/de07ffff-69a4-407b-9791-dfa1d6df685b
-- title:
--   Corollary 4.8 — recursion $\frac{\alpha_q}2F_q+\sum_{I\sim q}e^{2\lambda h(I)}\Delta_I\le\sqrt{\alpha_qF_q}\bigl(\sum_{q_\ell>0}\frac{\xi_\ell}{\omega_\ell}F_{q-e_\ell}\bigr)^{1/2}$
-- statement:
--   Assume $\omega>0$ and fix a nonzero $q=(q_0,\dots,q_L)$. For a state $\rho$, a Hamiltonian in the form (3.15), $\lambda=1/4$ and weights satisfying (4.2),
--   $$\frac{\alpha_q}2F_q+\sum_{I\sim q}e^{2\lambda h(I)}\Delta_I\ \le\ \sqrt{\alpha_qF_q}\Bigl(\sum_{\ell:q_\ell>0}\frac{\xi_\ell}{\omega_\ell}F_{q-e_\ell}\Bigr)^{1/2},\qquad(4.37)$$
--   where $\alpha_q=\sum_{\ell=0}^L q_\ell\omega_\ell$ and $\Delta_I=\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger[H,A_I])$ (4.38).
--
--   For a ground state every $\Delta_I\ge0$, and the inequality becomes a closed recursion for $F_q$ (Theorem 5.1).
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Corollary 4.8, Eqs. (4.37)–(4.38), p.25

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Corollary 4.8 (Recursion formula with commutator contribution)**, p.25, of J. Jiang, N. Ju,
O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum
impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (4.37)–(4.38).

Assume `ω > 0` and fix a nonzero `q = (q_0, …, q_L)`. Then
`(α_q/2) F_q + Σ_{I∼q} e^{2λh(I)} Δ_I ≤ √(α_q F_q) (Σ_{ℓ : q_ℓ > 0} (ξ_ℓ/ω_ℓ) F_{q−e_ℓ})^{1/2}`,
where `α_q = Σ_{ℓ=0}^{L} q_ℓ ω_ℓ` and `Δ_I = Re Tr(ρ A_I† [H, A_I])`.

**Formalization Note.** `ω > 0` is a field of `BandwiseForm`; `λ = 1/4` (4.5); the weights
satisfy (4.2) and `ρ` is a density matrix (standing assumptions of §4). -/
theorem corollary_4_8 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (hh : ValidWeights h)
    (ρ : FermiCap.Gaussian.Op n) (hρ : IsDensity ρ) (q : Fin (F.L + 1) → ℕ) (hq : q ≠ 0) :
    F.alphaQ q / 2 * F.Fq h ρ q +
        ∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) * F.DeltaI ρ I ≤
      Real.sqrt (F.alphaQ q * F.Fq h ρ q) *
        Real.sqrt (∑ ℓ ∈ Finset.univ.filter (fun ℓ => 0 < q ℓ),
          F.xi ℓ / F.omegaL ℓ * F.Fq h ρ (F.qMinus q ℓ)) := by sorry

end ImpuritySim
