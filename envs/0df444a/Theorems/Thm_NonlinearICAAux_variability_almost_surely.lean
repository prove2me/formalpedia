-- Prove2me | Theorems.Thm_NonlinearICAAux_variability_almost_surely
-- name    : NonlinearICAAux.variability_almost_surely
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:47:37.867713+00:00
-- url     : https://prove2.me/theorems/b46ff770-6a35-460e-9606-ad88b3e9cd60
-- title:
--   Theorem 2 (ii) (as proved): random natural parameters give the Assumption of Variability almost surely
-- statement:
--   Assume the nonlinear ICA model with auxiliary variables, with each $q_i(\cdot,\mathbf u)$ twice continuously differentiable, and suppose every source is conditionally exponential of the same order $k>1$:
--
--   $$p(s_i\mid\mathbf u)=\frac{Q_i(s_i)}{Z_i(\mathbf u)}\exp\sum_{j=1}^k\tilde q_{ij}(s_i)\lambda_{ij}(\mathbf u),$$
--
--   with twice continuously differentiable sufficient statistics $\tilde q_{ij}$. Assume:
--
--   1. for every $i$ and **every** $s\in\mathbb R$, the vectors $\big(\tilde q_{ij}'(s),\tilde q_{ij}''(s)\big)$, $j=1,\dots,k$, are not all proportional to each other, i.e. they span $\mathbb R^2$;
--   2. the vector of natural parameters $\boldsymbol\lambda(\mathbf u)\in\mathbb R^{nk}$ is measurable and, for $\mathbf u\sim\mu$, its law is absolutely continuous with respect to Lebesgue measure on $\mathbb R^{nk}$.
--
--   Then for every $\mathbf y\in\mathbb R^n$, if $\mathbf u_0,\dots,\mathbf u_{2n}$ are drawn independently from $\mu$, the vectors
--
--   $$\mathbf w(\mathbf y,\mathbf u_1)-\mathbf w(\mathbf y,\mathbf u_0),\ \dots,\ \mathbf w(\mathbf y,\mathbf u_{2n})-\mathbf w(\mathbf y,\mathbf u_0)$$
--
--   are linearly independent with probability one. In particular the Assumption of Variability holds.
--
--   **Formalization Note** The printed theorem requires the non-proportionality only for almost every $s$ and asks that the $\lambda$'s be statistically independent with a distribution "whose support has non-zero measure". The printed theorem is false under either of its two printed conditions (see the mission's report): the Assumption of Variability concerns every $\mathbf y$, and a distribution with atoms can have support of positive measure. The statement is what the proof in Supplementary B establishes; independent $\lambda_{ij}$ with absolutely continuous laws satisfy item 2.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Section 4.2, Theorem 2, item 2, p. 5; proof in Supplementary B, eqs. (28)-(31), p. 12

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem variability_almost_surely {n m k : ℕ} (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f) (hq : ∀ i u, ContDiff ℝ 2 (fun s => q i s u)) (hk : 1 < k)
    (Q : Fin n → ℝ → ℝ) (Z : Fin n → (Fin m → ℝ) → ℝ) (qt : Fin n → Fin k → ℝ → ℝ)
    (lam : Fin n → Fin k → (Fin m → ℝ) → ℝ)
    (hce : ∀ i, IsCondExpWith q i (Q i) (Z i) (qt i) (lam i))
    (hqt : ∀ i j, ContDiff ℝ 2 (qt i j))
    (hprop : ∀ (i : Fin n) (s : ℝ),
      Submodule.span ℝ (Set.range fun j : Fin k => ![deriv (qt i j) s, iteratedDeriv 2 (qt i j) s]) = ⊤)
    (hlam : Measurable (lamVec lam)) (hac : μ.map (lamVec lam) ≪ volume) :
    (∀ y : Fin n → ℝ, ∀ᵐ us ∂(Measure.pi fun _ : Fin (2 * n + 1) => μ),
      LinearIndependent ℝ (fun l : Fin (2 * n) => wVec q y (us l.succ) - wVec q y (us 0))) ∧
    Variability q := by sorry

end NonlinearICAAux
