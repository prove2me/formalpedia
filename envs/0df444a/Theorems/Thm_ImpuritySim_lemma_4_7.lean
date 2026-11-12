-- Prove2me | Theorems.Thm_ImpuritySim_lemma_4_7
-- name    : ImpuritySim.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:12.308688+00:00
-- url     : https://prove2.me/theorems/44dabbed-6e79-4e76-ae35-3cd3e3c9a007
-- title:
--   Lemma 4.7 — $|\sum_{I\sim q}e^{2\lambda h(I)}\mathrm{Tr}(\rho A_I^\dagger C_I)|\le\alpha_q^{1/2}\sqrt{F_q}(\sum_{q_\ell>0}\frac{\xi_\ell}{\omega_\ell}F_{q-e_\ell})^{1/2}$
-- statement:
--   Assume $\omega>0$, so that $\omega_\ell=2^\ell\omega>0$, and fix a nonzero $q=(q_0,\dots,q_L)$. For a state $\rho$, a Hamiltonian in the form (3.15), $\lambda=1/4$ and weights satisfying (4.2),
--   $$\Bigl|\sum_{I\sim q}e^{2\lambda h(I)}\operatorname{Tr}(\rho A_I^\dagger C_I)\Bigr|\ \le\ \alpha_q^{1/2}\sqrt{F_q}\Bigl(\sum_{\ell:q_\ell>0}\frac{\xi_\ell}{\omega_\ell}F_{q-e_\ell}\Bigr)^{1/2},\qquad \alpha_q:=\sum_\ell q_\ell\omega_\ell>0.\qquad(4.30),(4.31)$$
--
--   The hybridization term is controlled by the lower-order joint occupations $F_{q-e_\ell}$, which is what makes the recursion close.
--
--   **Formalization Note** $\omega>0$ is part of the form; the left side is a complex modulus; both the bound and $\alpha_q>0$ are stated.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 4.7, Eqs. (4.30)–(4.31), p.24

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Lemma 4.7 (Upper bound on the source term)**, p.24, of J. Jiang, N. Ju, O. Parekh,
C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (4.30)–(4.31).

Assume `ω > 0`, so that `ω_ℓ = 2^ℓ ω > 0`. Fix nonzero `q = (q_0, …, q_L)`. Then
`|Σ_{I∼q} e^{2λh(I)} Tr(ρ A_I† C_I)| ≤ α_q^{1/2} √F_q (Σ_{ℓ : q_ℓ > 0} (ξ_ℓ/ω_ℓ) F_{q−e_ℓ})^{1/2}`,
`α_q := Σ_ℓ q_ℓ ω_ℓ > 0`.

**Formalization Note.** `ω > 0` is a field of `BandwiseForm`; `λ = 1/4` (4.5); the weights
satisfy (4.2) and `ρ` is a density matrix (standing assumptions of §4). The left side is the
complex modulus; `√` is `Real.sqrt` of quantities that are nonnegative for a density matrix. Both
the bound and `α_q > 0` are stated. -/
theorem lemma_4_7 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (hh : ValidWeights h)
    (ρ : FermiCap.Gaussian.Op n) (hρ : IsDensity ρ) (q : Fin (F.L + 1) → ℕ) (hq : q ≠ 0) :
    ‖∑ I ∈ F.compatSets q,
        ((Real.exp (F.hI h I / 2) : ℝ) : ℂ) * (ρ * (AI n I)ᴴ * F.CI I).trace‖ ≤
      Real.sqrt (F.alphaQ q) * Real.sqrt (F.Fq h ρ q) *
        Real.sqrt (∑ ℓ ∈ Finset.univ.filter (fun ℓ => 0 < q ℓ),
          F.xi ℓ / F.omegaL ℓ * F.Fq h ρ (F.qMinus q ℓ)) ∧
      0 < F.alphaQ q := by sorry

end ImpuritySim
