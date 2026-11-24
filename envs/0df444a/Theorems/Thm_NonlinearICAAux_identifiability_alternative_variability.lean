-- Prove2me | Theorems.Thm_NonlinearICAAux_identifiability_alternative_variability
-- name    : NonlinearICAAux.identifiability_alternative_variability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:48:41.90723+00:00
-- url     : https://prove2.me/theorems/b77af011-6538-4063-84dc-8b7857ea82b8
-- title:
--   Supplementary D: Theorem 1 under the Alternative Assumption of Variability
-- statement:
--   Assume the hypotheses of Theorem 1 with two changes: each $q_i(s,\mathbf u)$ is three times continuously differentiable jointly in $(s,\mathbf u)\in\mathbb R\times\mathbb R^m$ (the auxiliary variable is continuous-valued), and the Assumption of Variability is replaced by the Alternative Assumption of Variability: for every $\mathbf y\in\mathbb R^n$ there are an index $j$ and $2n$ values $\mathbf u_1,\dots,\mathbf u_{2n}$ such that the vectors $\tilde{\mathbf w}(\mathbf y,\mathbf u_l)$,
--
--   $$\tilde{\mathbf w}(\mathbf y,\mathbf u)=\Big(\frac{\partial^2q_1(y_1,\mathbf u)}{\partial y_1\partial u_j},\dots,\frac{\partial^2q_n(y_n,\mathbf u)}{\partial y_n\partial u_j},\frac{\partial^3q_1(y_1,\mathbf u)}{\partial y_1^2\partial u_j},\dots,\frac{\partial^3q_n(y_n,\mathbf u)}{\partial y_n^2\partial u_j}\Big),$$
--
--   are linearly independent. If $\mathbf h$ is a $C^2$ diffeomorphism and $\sum_i\psi_i(h_i(\mathbf x),\mathbf u)=\log p(\mathbf x\mid\mathbf u)-\log p(\mathbf x)$ for all $\mathbf x,\mathbf u$, then there are a permutation $\sigma$ and bijections $\varphi_i$ with
--
--   $$h_i(\mathbf x)=\varphi_i\big(s_{\sigma(i)}\big)\qquad\text{for all }\mathbf x\text{ and }i.$$
--
--   **Formalization Note** The paper states "Theorem 1 holds with this alternative assumption as well". Joint $C^3$ smoothness is the regularity under which the mixed derivatives in $\tilde{\mathbf w}$ exist and the paper's differentiation in $u_j$ is valid. The paper's wording does not say "for any $\mathbf y$"; the quantifier is taken from the original Assumption of Variability, which the proof requires at every point. The index $j$ may depend on $\mathbf y$.
-- source:
--   Hyvärinen, Sasaki and Turner, Nonlinear ICA Using Auxiliary Variables and Generalized Contrastive Learning, arXiv:1805.08651v3 (AISTATS 2019), Supplementary D, eqs. (41)-(42), p. 13; Theorem 1, Section 4.2, pp. 4-5

import Mathlib
import Definitions.Def_NonlinearICAAux_Basic

open MeasureTheory
open scoped ENNReal

namespace NonlinearICAAux

theorem identifiability_alternative_variability {n m : ℕ} (μ : Measure (Fin m → ℝ))
    [IsProbabilityMeasure μ] (q : Fin n → ℝ → (Fin m → ℝ) → ℝ) (f : (Fin n → ℝ) ≃ (Fin n → ℝ))
    (hM : IsAuxICAModel μ q f)
    (hq : ∀ i, ContDiff ℝ 3 (fun p : ℝ × (Fin m → ℝ) => q i p.1 p.2))
    (hvar : AltVariability q)
    (h : (Fin n → ℝ) ≃ (Fin n → ℝ)) (hh : IsC2Diffeo h) (ψ : Fin n → ℝ → (Fin m → ℝ) → ℝ)
    (hopt : ∀ x u, regFun ψ h x u = logRatio μ q f x u) :
    ∃ σ : Equiv.Perm (Fin n), ∃ φ : Fin n → ℝ → ℝ, (∀ i, Function.Bijective (φ i)) ∧
      ∀ x i, h x i = φ i (f.symm x (σ i)) := by sorry

end NonlinearICAAux
