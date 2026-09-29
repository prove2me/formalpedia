-- Prove2me | Theorems.Thm_HighDimStat_Pca_pca_eigenvector_perturbation_bound
-- name    : HighDimStat.Pca.pca_eigenvector_perturbation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:14:47.671977+00:00
-- url     : https://prove2.me/theorems/ef6f1879-d0b6-46af-b604-483883adb140
-- title:
--   Eigenvector perturbation bound for high-dimensional PCA (Theorem 8.5)
-- statement:
--   **Theorem 8.5.** Consider a positive semidefinite, symmetric matrix $M$ with maximum unit
--   eigenvector $\theta^*$ and eigengap $\nu=\gamma_1(M)-\gamma_2(M)>0$. Given any symmetric
--   matrix $P$ with $|\!|\!|P|\!|\!|_2 < \nu/2$, let $\hat\theta$ be a maximal unit eigenvector
--   of the perturbed matrix $\hat M := M+P$, sign-resolved so that $\langle\hat\theta,\theta^*
--   \rangle \ge 0$. Then
--
--   $$
--   \|\hat\theta - \theta^*\|_2 \;\le\; \frac{2\|\tilde p\|_2}{\nu - 2|\!|\!|P|\!|\!|_2}.
--   $$
--
--   This is the chapter's title result: a fully deterministic guarantee that the top
--   eigenvector of a perturbed matrix stays close to the original, in terms of a
--   perturbation-specific quantity $\|\tilde p\|_2$ (not the whole operator norm
--   $|\!|\!|P|\!|\!|_2$) whenever the eigengap dominates the perturbation's overall size.
--
--   **Formalization Note** The book's own theorem statement additionally asserts that $\hat M$
--   "has a *unique* maximal eigenvector $\hat\theta$" as part of its conclusion; this mission
--   formalizes only the quantitative distance bound, for an arbitrary maximal unit eigenvector
--   $\hat\theta$ of $\hat M$ satisfying the sign condition, since that is exactly what the
--   book's own proof establishes and exactly what every downstream use in the chapter
--   (Examples, Corollary 8.7) actually invokes — see `description.md`'s Formalization scope for
--   the full disclosure of this deliberate scope decision. The hypothesis $|\!|\!|P|\!|\!|_2 <
--   \nu/2$ is preserved exactly (a sharp threshold per the book's own $2\times2$
--   counterexample, not weakened).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 243 (PDF p. 263), Theorem 8.5, Eq. (8.12)

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_OpNormSymm
import Definitions.Def_HighDimStat_Pca_Ptilde
import Definitions.Def_HighDimStat_Pca_L2Norm

namespace HighDimStat.Pca

/-- **Theorem 8.5**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (8.12), p. 243.
Consider a positive semidefinite, symmetric matrix `M` with maximum unit eigenvector `θ*` and
eigengap `ν = γ₁(M) − γ₂(M) > 0`. Given any symmetric matrix `P` with `|||P|||₂ < ν/2`, and
`θ̂` a maximal unit eigenvector of the perturbed matrix `M̂ := M + P` with sign resolved so
that `⟨θ̂,θ*⟩ ≥ 0`, then `‖θ̂ − θ*‖₂ ≤ 2‖p̃‖₂ / (ν − 2|||P|||₂)`. -/
theorem pca_eigenvector_perturbation_bound {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hMsym : M.transpose = M)
    (hMpsd : ∀ v : Fin d → ℝ, 0 ≤ ∑ i, v i * (M.mulVec v) i)
    (hPsym : P.transpose = P)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hPop : opNormSymm P < ν / 2)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat)
    (hsign : 0 ≤ ∑ j, θhat j * θstar j) :
    l2Norm (fun j => θhat j - θstar j) ≤
      (2 * l2Norm (ptilde P θstar)) / (ν - 2 * opNormSymm P) := by sorry

end HighDimStat.Pca
