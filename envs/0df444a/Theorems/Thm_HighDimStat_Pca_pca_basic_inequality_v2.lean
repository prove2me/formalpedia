-- Prove2me | Theorems.Thm_HighDimStat_Pca_pca_basic_inequality_v2
-- name    : HighDimStat.Pca.pca_basic_inequality_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:23.870029+00:00
-- url     : https://prove2.me/theorems/2b1a7bfd-83e5-4944-8553-d44a58df93d4
-- title:
--   The PCA basic inequality (Lemma 8.6), for symmetric matrices
-- statement:
--   **Lemma 8.6** (PCA basic inequality). Let $M$ and $M+P$ be symmetric $d\times d$ matrices
--   (in the chapter's setting $M=\Sigma$ is the population covariance, $M+P=\hat\Sigma$ the sample
--   covariance, so the perturbation $P=\hat\Sigma-\Sigma$ is symmetric). Given that $M$ has
--   eigengap $\nu>0$ at its maximal unit eigenvector $\theta^*$, and $\hat\theta$ is a maximal
--   unit eigenvector of the perturbed matrix $M+P$, the error $\Delta=\hat\theta-\theta^*$ satisfies
--
--   $$
--   \nu\bigl(1 - \langle\hat\theta,\theta^*\rangle^2\bigr) \;\le\; |\Psi(\Delta; P)|,
--   \qquad \Psi(\Delta;P)=\langle\Delta,P\Delta\rangle+2\langle\Delta,P\theta^*\rangle .
--   $$
--
--   This is the technical core that Theorem 8.5's proof builds its final bound on: it converts
--   the abstract optimality of $\hat\theta$ and $\theta^*$ for their respective quadratic
--   programs into a concrete inequality relating the eigengap, the alignment
--   $\langle\hat\theta,\theta^*\rangle$, and the perturbation.
--
--   **Formalization Note.** The retired version (`pca_basic_inequality`) took arbitrary real
--   matrices $M$, $P$; Rayleigh quotients only see the symmetric part of $P$ while $\Psi$ also sees
--   its antisymmetric part through $\langle\Delta,P\theta^*\rangle$, and the proof uses
--   $\langle\theta^*,P\Delta\rangle=\langle\Delta,P\theta^*\rangle$, so the lemma fails for
--   non-symmetric $P$ (accepted disproof in $d=2$). The new statement adds `hMsymm : M.IsSymm` and
--   `hPsymm : P.IsSymm`, the chapter's standing assumption that $\Sigma$ and $\hat\Sigma$ are
--   covariance (symmetric) matrices; positive semidefiniteness is not needed for the lemma and is
--   not assumed. As before, the lemma is stated for $C=\mathcal S^{d-1}$ (the full sphere), the
--   case used in the proof of Theorem 8.5, with `IsMaximalUnitEigenvector` the variational
--   characterization (8.14) and `HasEigengap` the Courant–Fischer form of $\nu=\gamma_1-\gamma_2>0$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 243 (PDF p. 263), Lemma 8.6, Eq. (8.15)

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_PsiPCA

namespace HighDimStat.Pca

/-- **Lemma 8.6** (PCA basic inequality), Wainwright, *High-Dimensional Statistics* (2019),
Eq. (8.15), p. 243. Given a **symmetric** matrix `M` (the population covariance `Σ`) with
eigengap `ν > 0` at its maximal unit eigenvector `θ*`, and `θ̂` a maximal unit eigenvector of
the **symmetric** perturbed matrix `M̂ = M + P` (the sample covariance `Σ̂`, so that the
perturbation `P = Σ̂ − Σ` is symmetric), the error `Δ = θ̂ − θ*` is bounded as
`ν(1 − ⟨θ̂,θ*⟩²) ≤ |Ψ(Δ; P)|`, with `Ψ(Δ; P) = ⟨Δ, PΔ⟩ + 2⟨Δ, Pθ*⟩`.

Correction relative to the retired version: the chapter's standing assumption that `Σ` and
`Σ̂` are covariance (hence symmetric) matrices was dropped; the proof uses
`⟨θ*, PΔ⟩ = ⟨Δ, Pθ*⟩`, and Rayleigh quotients only see the symmetric part of `P` while `Ψ`
also sees its antisymmetric part, so the lemma fails for non-symmetric `P`. -/
theorem pca_basic_inequality_v2 {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (hMsymm : M.IsSymm) (hPsymm : P.IsSymm)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat) :
    ν * (1 - (∑ j, θhat j * θstar j) ^ 2) ≤
      |psiPCA P θstar (fun j => θhat j - θstar j)| := by sorry

end HighDimStat.Pca
