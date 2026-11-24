-- Prove2me | Theorems.Thm_LearnThenTest_hoeffding_bentkus_pvalue_valid
-- name    : LearnThenTest.hoeffding_bentkus_pvalue_valid
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:08:28.551295+00:00
-- url     : https://prove2.me/theorems/38d26a70-0b32-4148-8bc2-e252b929fbfa
-- title:
--   Proposition 1: Hoeffding–Bentkus p-values are valid
-- statement:
--   Let $n\ge1$ and let $L_1,\dots,L_n$ be independent and identically distributed losses with values in $[0,1]$, the losses $L_i=L(\mathcal T_{\lambda_j}(X_i),Y_i)$ of a fixed $\lambda_j$ on an i.i.d. calibration set. Their mean is the risk $R(\lambda_j)=\mathbb E[L_1]$. Let $0<\alpha<1$ and suppose the null hypothesis $\mathcal H_j:R(\lambda_j)>\alpha$ holds. Let $\hat R=\frac1n\sum_{i=1}^nL_i$ and $h_1(a,b)=a\log(a/b)+(1-a)\log((1-a)/(1-b))$. Then
--
--   $$p^{\mathrm{HB}}=\min\Big(\exp\{-n\,h_1(\hat R\wedge\alpha,\alpha)\},\ e\,\mathbb P\big(\mathrm{Bin}(n,\alpha)\le\lceil n\hat R\rceil\big)\Big)$$
--
--   is a valid p-value: $\mathbb P(p^{\mathrm{HB}}\le u)\le u$ for every $u\in[0,1]$.
--
--   This is the p-value the paper uses in all of its finite-sample experiments.
--
--   **Formalization Note** The losses are taken directly as i.i.d. random variables, without modelling the data $(X_i,Y_i)$ and the predictor. The restriction $0<\alpha<1$ is not printed, but it is needed for $h_1(\cdot,\alpha)$ and $\mathrm{Bin}(n,\alpha)$ to be defined.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.2, Proposition 1, eq. (1), p. 4; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem hoeffding_bentkus_pvalue_valid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n) (L : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (L i)) (hind : iIndepFun L P)
    (hident : ∀ i, IdentDistrib (L i) (L ⟨0, hn⟩) P P)
    (hL01 : ∀ i ω, L i ω ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (hnull : α < ∫ ω, L ⟨0, hn⟩ ω ∂P) :
    IsValidPValue P (fun ω => hbPValue n α (empRisk (fun i => L i ω))) := by sorry

end LearnThenTest
