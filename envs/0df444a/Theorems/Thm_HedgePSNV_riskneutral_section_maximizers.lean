-- Prove2me | Theorems.Thm_HedgePSNV_riskneutral_section_maximizers
-- name    : HedgePSNV.riskneutral_section_maximizers
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:05:35.451719+00:00
-- url     : https://prove2.me/theorems/eff9ec14-0083-4078-8243-4cd8de8b6457
-- title:
--   Section maximizers of $V(P,R)=\mathbb E[H_T(P,R)]$ over the decision domain exist and are monotone (strictly positive cross-partial $1-F(R)$)
-- statement:
--   Let $\nu$ be a probability law of a market size $A$ on $\mathbb R$ with $\mathbb E[A^-]<\infty$ satisfying Assumption 1, and let $V(P,R)=\mathbb E_\nu[H_T(P,R)]=\mathbb E_\nu[(P-c)(R-bP)-(P-s)(R-A)^+]$. On the decision domain $D=\{P\ge c,\ R-bP\ge 0\}$:
--
--   1. $V$ is continuous;
--   2. for each $P\ge c$ the section $R\mapsto V(P,R)$ has a maximizer $R^{NV}(P)$ over $\{R\ge bP\}$, and for each $R\ge bc$ the section $P\mapsto V(P,R)$ has a maximizer $P^{NV}(R)$ over $\{c\le P\le R/b\}$;
--   3. the section maximizers are monotone:
--
--   $$c\le P_1\le P_2\ \Rightarrow\ R^{NV}(P_1)\le R^{NV}(P_2),\qquad R_1\le R_2\ \Rightarrow\ P^{NV}(R_1)\le P^{NV}(R_2),$$
--
--   for any choice of maximizers.
--
--   Role: Proposition 5 (EC.8.2) combines Lemma EC.7 ($P^h_m\le P^{NV(M)}(R^h_m)$, $R^h_m\le R^{NV(M)}(P^h_m)$) with the monotonicity of these section maximizers for the risk-neutral law of $A_T$, and uses the continuity of $V_0$ for an intermediate-value step.
--
--   **Formalization Note**: the paper writes the unconstrained section argmaxes $P^{NV(M)}(R)=(bc+\mathbb E^M(R\wedge A_T))/(2b)$ and $R^{NV(M)}(P)=F_M^{-1}((P-c)/(P-s))$ of (EC.8.9); since every argmax in the paper is read over $D$ (p.9), the sections here are the sections of $D$, matching the formal Lemma EC.7.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, EC.8.2, proof of Proposition 7, p.ec49: V_0 concave in P (resp. R) for fixed R (resp. P), section maximizers P^{NV(M)}(R), R^{NV(M)}(P) of (EC.8.9), increasing in R (resp. P); applied to a general law satisfying Assumption 1 (p.8)

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem riskneutral_section_maximizers (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun a : ℝ => max (-a) 0) ν) (h1 : Assumption1 ν) :
    Continuous (fun q : ℝ × ℝ => nvValue p ν id q.1 q.2) ∧
    (∀ P, p.c ≤ P → ∃ R, p.b * P ≤ R ∧
      ∀ R', p.b * P ≤ R' → nvValue p ν id P R' ≤ nvValue p ν id P R) ∧
    (∀ R, p.b * p.c ≤ R → ∃ P, p.c ≤ P ∧ p.b * P ≤ R ∧
      ∀ P', p.c ≤ P' → p.b * P' ≤ R → nvValue p ν id P' R ≤ nvValue p ν id P R) ∧
    (∀ P1 P2 R1 R2, p.c ≤ P1 → P1 ≤ P2 →
      (p.b * P1 ≤ R1 ∧ ∀ R', p.b * P1 ≤ R' → nvValue p ν id P1 R' ≤ nvValue p ν id P1 R1) →
      (p.b * P2 ≤ R2 ∧ ∀ R', p.b * P2 ≤ R' → nvValue p ν id P2 R' ≤ nvValue p ν id P2 R2) →
      R1 ≤ R2) ∧
    (∀ R1 R2 P1 P2, R1 ≤ R2 →
      (p.c ≤ P1 ∧ p.b * P1 ≤ R1 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R1 → nvValue p ν id P' R1 ≤ nvValue p ν id P1 R1) →
      (p.c ≤ P2 ∧ p.b * P2 ≤ R2 ∧
        ∀ P', p.c ≤ P' → p.b * P' ≤ R2 → nvValue p ν id P' R2 ≤ nvValue p ν id P2 R2) →
      P1 ≤ P2) := by sorry

end HedgePSNV
