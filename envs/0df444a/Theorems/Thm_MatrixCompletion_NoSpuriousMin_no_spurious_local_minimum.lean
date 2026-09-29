-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_no_spurious_local_minimum
-- name    : MatrixCompletion.NoSpuriousMin.no_spurious_local_minimum
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:55.679867+00:00
-- url     : https://prove2.me/theorems/7df638ff-144d-41a3-b753-6868d428a18a
-- title:
--   Matrix completion has no spurious local minimum (GLM Thm 5.3, in Chen–Li Cor 2.2 form)
-- statement:
--   **The goal theorem.** Let $M=ZZ^\top$ with $Z\in\mathbb{R}^{d\times r}$ $\mu$-incoherent (row version, Ge–Lee–Ma Assumption 1), $\|Z\|_F^2=r$, condition number $\sigma_{\max}(Z)\le\kappa\,\sigma_{\min}(Z)$, $\sigma_{\min}(Z)>0$. Choose the tuning parameters data-adaptively in Chen–Li's windows: $100\,\|Z\|_{2\to\infty}\le\alpha\le200\,\|Z\|_{2\to\infty}$ and $100\,\|\Omega-pJ\|\le\lambda\le200\,\|\Omega-pJ\|$, with sampling rate $p\ge 10^{10}\mu^4\kappa^4r^2\log d/d$. Assume the observation set $\Omega$ is a good sample — symmetric, with bounded row counts, the spectral bound $\|\Omega-pJ\|\le100(\sqrt{dp}+\sqrt{\log d})$, and tangent-space concentration. Then every local minimum $X$ of the regularized objective
--
--   $$f(X)=\tfrac12\bigl\|P_\Omega(M-XX^\top)\bigr\|_F^2+\lambda\sum_{i=1}^d(\|X_i\|-\alpha)_+^4$$
--
--   is a global minimum: $f(X)=0$ and $XX^\top=ZZ^\top$. Non-convexity notwithstanding, the landscape hides no traps — which is why gradient descent from arbitrary initialization provably solves positive semidefinite matrix completion.
--
--   **Formalization Note** This is the deterministic core of the high-probability statement: the randomness of $\Omega$ factors through the good-sample predicate (Chen–Li Lemmas 4.1–4.2), whose probabilistic verification is a follow-up mission. The theorem is Ge–Lee–Ma's (their Theorem 5.3), formalized in the strengthened Chen–Li form (Corollary 2.2: data-driven tuning, sampling rate improving Ge–Lee–Ma's $\mu^6\kappa^{16}$ and Ge–Jin–Zheng's $\mu^3r^4\kappa^4$ regimes) via the Ge–Jin–Zheng auxiliary-function route. Local minimality is Lean's topological IsLocalMin on $\mathbb{R}^{d\times r}$.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], p. 8, Corollary 2.2 (exact recovery at every local minimum; deterministic core). Provenance: the theorem originates as Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), p. 11, Theorem 5.3, and improves Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, Theorem 12.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Matrix
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.no_spurious_local_minimum
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hgood : GoodSample Z Ω p)
    (hmin : IsLocalMin (objective Z Ω lam α) X) :
    objective Z Ω lam α X = 0 ∧ X * Xᵀ = Z * Zᵀ := by sorry
