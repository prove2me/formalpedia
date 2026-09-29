-- Prove2me | Theorems.Thm_HighDimStat_Pca_pca_basic_inequality
-- name    : HighDimStat.Pca.pca_basic_inequality
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:13:55.906713+00:00
-- url     : https://prove2.me/theorems/3a5b2fd6-d506-473a-bd53-d979d71d6b9d
-- title:
--   The PCA basic inequality (Lemma 8.6)
-- statement:
--   **Lemma 8.6** (PCA basic inequality). Given a matrix $M$ with eigengap $\nu>0$ at its
--   maximal unit eigenvector $\theta^*$, and $\hat\theta$ a maximal unit eigenvector of the
--   perturbed matrix $\hat M = M+P$, the error $\Delta = \hat\theta - \theta^*$ satisfies
--
--   $$
--   \nu\bigl(1 - \langle\hat\theta,\theta^*\rangle^2\bigr) \;\le\; |\Psi(\Delta; P)|.
--   $$
--
--   This is the technical core that Theorem 8.5's proof builds its final bound on: it converts
--   the abstract optimality of $\hat\theta$ and $\theta^*$ for their respective quadratic
--   programs into a concrete inequality relating the eigengap, the alignment
--   $\langle\hat\theta,\theta^*\rangle$, and the perturbation.
--
--   **Formalization Note** Stated for the case $C = \mathcal S^{d-1}$ (the full sphere), which
--   is the only case the book's own proof of Theorem 8.5 uses, rather than the fully general
--   subset $C \subseteq \mathcal S^{d-1}$ the book's Lemma 8.6 statement allows for (the book
--   itself notes "we state this inequality in a slightly more general form than required for
--   the current proof... the current proof involves the choice $C = \mathcal S^{d-1}$" — this
--   mission formalizes exactly that instantiated case).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 243 (PDF p. 263), Lemma 8.6, Eq. (8.15)

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_PsiPCA

namespace HighDimStat.Pca

/-- **Lemma 8.6** (PCA basic inequality), Wainwright, *High-Dimensional Statistics* (2019),
Eq. (8.15), p. 243. Given a matrix `M` with eigengap `ν > 0` at its maximal unit eigenvector
`θ*`, and `θ̂` a maximal unit eigenvector of the perturbed matrix `M̂ = M + P`, the error
`Δ = θ̂ − θ*` is bounded as `ν(1 − ⟨θ̂,θ*⟩²) ≤ |Ψ(Δ; P)|`. -/
theorem pca_basic_inequality {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat) :
    ν * (1 - (∑ j, θhat j * θstar j) ^ 2) ≤
      |psiPCA P θstar (fun j => θhat j - θstar j)| := by sorry

end HighDimStat.Pca
