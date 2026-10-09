-- Prove2me | Theorems.Thm_GaussianMatrix_full_rank_ae
-- name    : GaussianMatrix.full_rank_ae
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:36:40.10871+00:00
-- url     : https://prove2.me/theorems/6b3ff8e9-6ff5-4084-9bad-3b255d3e8159
-- title:
--   A standard Gaussian matrix has full rank almost surely
-- statement:
--   Let $\Gamma\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then, almost surely,
--   $$\operatorname{rank}\Gamma=\min\{p,m\}.$$
--
--   Equivalently, a wide ($p\le m$) Gaussian matrix has full row rank and $\Gamma\Gamma^{\mathsf T}$ is invertible almost surely; a tall one has full column rank. This is the structural fact that makes the pseudoinverse $\Omega_1^{\dagger}=\Omega_1^{\mathsf T}(\Omega_1\Omega_1^{\mathsf T})^{-1}$ well defined with probability one in the analysis of randomized range finders, and that lets one treat $(GG^{\mathsf T})^{-1}$ as the inverse-Wishart matrix.
--
--   **Formalization Note.** `rank` is Mathlib's matrix rank over $\mathbb R$; the statement is a $\gamma_{p,m}$-almost-everywhere equality, with no restriction on $p,m$ (for $p=0$ or $m=0$ both sides are $0$).
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.2 p. 57, proof of Theorem 10.5: "the rows of a (fat) Gaussian matrix are almost surely in general position, so the k × (k + p) matrix Ω₁ has full row rank with probability one"; Appendix A.2 p. 65, proof of Proposition A.5: "the Wishart matrix GG* is invertible with probability one". Stated for arbitrary $p\times m$ as $\operatorname{rank}=\min(p,m)$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem full_rank_ae (p m : ℕ) :
    ∀ᵐ G ∂(gaussianMatrix p m), (Matrix.of G).rank = min p m := by sorry
end GaussianMatrix
