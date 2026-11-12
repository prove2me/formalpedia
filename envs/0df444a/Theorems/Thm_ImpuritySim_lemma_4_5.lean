-- Prove2me | Theorems.Thm_ImpuritySim_lemma_4_5
-- name    : ImpuritySim.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:17.425957+00:00
-- url     : https://prove2.me/theorems/57f7bfc6-00f2-4779-81df-a4c6ea7b3ff2
-- title:
--   Lemma 4.5 — $\mathrm{Tr}[\mathrm{Re}(e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell})M^{J\ell}]\ge\frac{\omega_\ell}2\mathrm{Tr}(M^{J\ell})=\frac{\omega_\ell}2\sum_{j}\mathrm{Tr}(\rho_{J\cup\{j\}})$
-- statement:
--   Let $\rho$ be a state, $H$ in the form (3.15), $\lambda=1/4$, and let the weights satisfy (4.2). For every increasing list $J$ of residual-bath modes and every band $\ell\in\{0,\dots,L\}$,
--   $$\operatorname{Tr}\bigl[\operatorname{Re}(e^{-\lambda D_\ell}E_\ell e^{\lambda D_\ell})M^{J\ell}\bigr]\ \ge\ \frac{\omega_\ell}2\operatorname{Tr}(M^{J\ell})\ =\ \frac{\omega_\ell}2\sum_{j:\ell(j)=\ell,\ j\notin J}\operatorname{Tr}(\rho_{J\cup\{j\}}),\qquad(4.25)$$
--   with $M^{J\ell}$ the correlation matrix (4.24) and $j$ ranging over the band-$\ell$ residual-bath modes.
--
--   **Formalization Note** Both clauses are stated: the inequality between the (real) traces, and the identity $\operatorname{Tr}(M^{J\ell})=\sum_j\operatorname{Tr}(\rho_{J\cup\{j\}})$.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - encoding: the traces in (4.25), real numbers → the inequality between real parts of the traces; the equality Tr(M^{Jℓ}) = Σ_j Tr(ρ_{J∪{j}}) as complex numbers; reason: both traces are real; the complex equality implies the real one
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Lemma 4.5, Eq. (4.25), p.24; (4.23)–(4.24), p.23

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Lemma 4.5 (Single-particle bath-energy bound)**, p.24, of J. Jiang, N. Ju, O. Parekh,
C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (4.25).

For any fixed increasing list `J` of residual-bath modes and any band `ℓ`,
`Tr[Re(e^{−λD_ℓ} E_ℓ e^{λD_ℓ}) M^{Jℓ}] ≥ (ω_ℓ/2) Tr(M^{Jℓ}) = (ω_ℓ/2) Σ_{j : ℓ(j) = ℓ, j ∉ J} Tr(ρ_{J∪{j}})`.

**Formalization Note.** `λ = 1/4` (4.5); the weights satisfy (4.2) and `ρ` is a density matrix
(standing assumptions of §4). Both clauses are stated: the inequality between the real parts of
the traces (both traces are real), and the equality `Tr(M^{Jℓ}) = Σ_j Tr(ρ_{J∪{j}})` as complex
numbers, `j` ranging over the band-`ℓ` residual-bath modes not in `J`. -/
theorem lemma_4_5 {n : ℕ} (F : BandwiseForm n) (h : ℕ → ℝ) (hh : ValidWeights h)
    (ρ : FermiCap.Gaussian.Op n) (hρ : IsDensity ρ) (J : Finset (Fin n)) (hJ : J ⊆ F.bath)
    (ℓ : ℕ) (hℓ : ℓ ≤ F.L) :
    F.omegaL ℓ / 2 * (F.Mcorr h ρ J ℓ).trace.re ≤
        (F.reSimE h (1 / 4) ℓ * F.Mcorr h ρ J ℓ).trace.re ∧
      (F.Mcorr h ρ J ℓ).trace =
        ∑ j ∈ F.bath.filter (fun j => F.band j = ℓ ∧ j ∉ J), (F.rhoI h ρ (insert j J)).trace := by sorry

end ImpuritySim
