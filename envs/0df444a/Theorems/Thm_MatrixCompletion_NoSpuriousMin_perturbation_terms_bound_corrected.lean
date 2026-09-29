-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_perturbation_terms_bound_corrected
-- name    : MatrixCompletion.NoSpuriousMin.perturbation_terms_bound_corrected
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-14T18:52:35.368449+00:00
-- url     : https://prove2.me/theorems/181879e0-08a2-4a2a-9be2-e99d62d629fa
-- title:
--   Perturbation terms bound (Chen–Li Lemma 4.8, exact rank, corrected constants)
-- statement:
--   **Chen–Li Lemma 4.8 (exact-rank case), with usable constants.**
--
--   Let $M=ZZ^\top$ with $Z\in\mathbb R^{d\times r}$ $\mu$-incoherent, $\|Z\|_F^2=r$, $\sigma_{\max}(Z)\le\kappa\sigma_{\min}(Z)$ and $\sigma_{\min}(Z)>0$; let $\Omega$ be a good sample at rate $p$, let $U$ be an aligned exact factor ($UU^\top=ZZ^\top$, $X^\top U\succeq0$) and put $\Delta=X-U$. Choose the tuning parameters in Chen–Li's windows, $100\|Z\|_{2\to\infty}\le\alpha\le200\|Z\|_{2\to\infty}$ and $100\|\Omega-pJ\|\le\lambda\le200\|\Omega-pJ\|$. If moreover the sampling rate satisfies
--
--   $$p\;\ge\;\frac{10^{28}\,\mu^4\kappa^4r^2\,(1+\log d)}{d},$$
--
--   then, uniformly over all $X$,
--
--   $$D_{\Omega,p}(\Delta\Delta^\top,\Delta\Delta^\top)-3D_{\Omega,p}(XX^\top-UU^\top,XX^\top-UU^\top)+\lambda\Bigl(\langle\Delta,\nabla^2R_\alpha(X)[\Delta]\rangle-4\langle\nabla R_\alpha(X),\Delta\rangle\Bigr)\;\le\;\frac{p}{50}\Bigl(\|\Delta^\top\Delta\|_F^2+\|U\Delta^\top\|_F^2\Bigr).$$
--
--   This is $\sum_{i=2}^{4}K_i(X)$ of Chen–Li's decomposition, with $K_4=0$ in the exact-rank case.
--
--   **Why the constants differ from the mission's `perturbation_terms_bound`.** That statement asserts the same inequality with the mission's `SampleCondition` ($C=10^{10}$) and $p/1000$ on the right; it is **false**, and an explicit machine-checked counterexample is recorded on the platform (theorem `c21e6513-94ab-4c7b-980d-7dde5be7a71c`, disproof `a797f42a-1928-4b1b-90ab-2234a526d06e`). Two independent constants are too small.
--
--   1. *The sampling rate.* The binding term is $\lambda\alpha^2\|\Delta\|_F^2$. Within the statement's own windows $\lambda$ reaches $200\|\Omega-pJ\|$ and $\alpha^2$ reaches $4\cdot10^4\nu_r$, and the sharp constant in Lemma 4.10 is about $50$, so absorbing it into $\tfrac{p}{1000}\sigma_{\min}(Z)^2\|\Delta\|_F^2$ needs $pd\gtrsim10^{27}\mu^4r^2\kappa^4$. `SampleCondition` supplies only $pd\ge10^{10}\mu^4\kappa^4r^2\log d$ — short by roughly eighteen orders of magnitude. Chen–Li write "for a sufficiently large absolute constant $C$"; $10^{28}$ is large enough, $10^{10}$ is not.
--
--   2. *The target accuracy.* Chen–Li's eq. (4.29) applies their Lemma 4.2 at relative accuracy $\delta=2.5\times10^{-5}$, which is what turns $3|D_{\Omega,p}(U\Delta^\top+\Delta U^\top,\cdot)|$ into $10^{-4}p\|U\Delta^\top\|_F^2$. The mission's `GoodSample.tangent_conc` field only offers $p/1000$, and $\|U\Delta^\top+\Delta U^\top\|_F^2\le4\|U\Delta^\top\|_F^2$, so this term costs $1.2\times10^{-2}\,p\,\|U\Delta^\top\|_F^2$ — already past a $p/1000$ budget. The constant $1/50$ is what the good-sample hypothesis as curated can actually pay for, and it is still small enough to keep the resulting quadratic form negative definite (see `K_superlevel_bound_corrected`).
--
--   Everything else is Chen–Li's argument verbatim. Because `tangent_conc` is stated for the tangent space of $\operatorname{col}(Z)$ itself and $UU^\top=ZZ^\top$, the whole matrix $U\Delta^\top+\Delta U^\top$ is tangent, so the spectral truncation of §4.3.3 (the index $s$, the incoherence of the leading columns $U^1$) is not needed: it collapses to the exact case $s=r$.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3), p. 19, Lemma 4.8 (eq. 4.7), exact-rank specialization, with Chen-Li's unspecified absolute constant C instantiated at 10^28 rather than 10^10 and the accuracy 10^-3 relaxed to 1/50.  Proof: Lemma 4.9 (p. 25, section 4.3.3) plus Lemma 4.10 (p. 23, Appendix B).  The 10^10/10^-3 instantiation is refuted by the counterexample in submission a797f42a-1928-4b1b-90ab-2234a526d06e against theorem c21e6513-94ab-4c7b-980d-7dde5be7a71c.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.perturbation_terms_bound_corrected
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    sampDev Ω p ((X - U) * (X - U)ᵀ) ((X - U) * (X - U)ᵀ)
        - 3 * sampDev Ω p (X * Xᵀ - U * Uᵀ) (X * Xᵀ - U * Uᵀ)
        + lam * (regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)) ≤
      p / 50 * (frobSq ((X - U)ᵀ * (X - U)) + frobSq (U * (X - U)ᵀ)) := by sorry
