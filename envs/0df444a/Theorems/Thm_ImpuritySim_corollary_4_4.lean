-- Prove2me | Theorems.Thm_ImpuritySim_corollary_4_4
-- name    : ImpuritySim.corollary_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:10.785636+00:00
-- url     : https://prove2.me/theorems/116ed784-1957-4690-9a17-7aee1868e6f3
-- title:
--   Corollary 4.4 — $-\sum_{I\sim q}e^{2\lambda h(I)}\Delta_I=\sum_{I\sim q}e^{2\lambda h(I)}\mathrm{Re\,Tr}(\rho A_I^\dagger B_I)+\sum_{I\sim q}e^{2\lambda h(I)}\mathrm{Re\,Tr}(\rho A_I^\dagger C_I)$
-- statement:
--   Fix a nonzero $q=(q_0,\dots,q_L)$. For a state $\rho$ and a Hamiltonian in the form (3.15), with $\lambda=1/4$,
--   $$-\sum_{I\sim q}e^{2\lambda h(I)}\Delta_I=\sum_{I\sim q}e^{2\lambda h(I)}\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger B_I)+\sum_{I\sim q}e^{2\lambda h(I)}\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger C_I),\qquad(4.22)$$
--   where $\Delta_I=\operatorname{Re}\operatorname{Tr}(\rho A_I^\dagger[H,A_I])$.
--
--   The left side carries the only state-dependent information; the two terms on the right are bounded in Lemmas 4.6 and 4.7.
--
--   **Formalization Note** $\rho$ is a density matrix and the weights satisfy (4.2), the standing assumptions of §4.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Corollary 4.4, Eq. (4.22), p.23

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Corollary 4.4**, p.23, of J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time
classical and quantum simulation of quantum impurity models*, arXiv:2610.02167 (held version,
sha256 88d2a4e6…f0fff9b2), Eq. (4.22).

Fix nonzero `q = (q_0, …, q_L)`. For a state `ρ` and an impurity Hamiltonian in the form (3.15),
`−Σ_{I∼q} e^{2λh(I)} Δ_I = Σ_{I∼q} e^{2λh(I)} Re Tr(ρ A_I† B_I) + Σ_{I∼q} e^{2λh(I)} Re Tr(ρ A_I† C_I)`.

**Formalization Note.** `λ = 1/4` (4.5), so `e^{2λh(I)} = e^{h(I)/2}`; the weights satisfy (4.2)
and `ρ` is a density matrix (the standing assumptions of §4); `I ∼ q` ranges over `compatSets q`;
`Δ_I = Re Tr(ρ A_I† [H, A_I])` (4.21). -/
theorem corollary_4_4 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (hh : ValidWeights h)
    (ρ : FermiCap.Gaussian.Op n) (hρ : IsDensity ρ) (q : Fin (F.L + 1) → ℕ) (hq : q ≠ 0) :
    -(∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) * F.DeltaI ρ I) =
      (∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) * (ρ * (AI n I)ᴴ * F.BI I).trace.re) +
        ∑ I ∈ F.compatSets q, Real.exp (F.hI h I / 2) * (ρ * (AI n I)ᴴ * F.CI I).trace.re := by sorry

end ImpuritySim
