-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_assumption1_case_i
-- name    : GDPRDataMarkets.Rights.assumption1_case_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:06.624752+00:00
-- url     : https://prove2.me/theorems/6838909a-f2e0-4aaa-b93e-7b110b8a0ef4
-- title:
--   §3.1, p. 15 — Assumption 1 implies 2(κ_L v − c) ≥ κ_H v − c ≥ 0 for every v ≥ v*_M(p₁)
-- statement:
--   Assume $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$ and Assumption 1, $\mu\ge\max\{(3+\delta)\sigma,\ \tfrac12+(2+\delta)\sigma\}$. Let $p_1\in\mathbb R$ and let $v^*_M(p_1)=\max\{c/(\delta\sigma),\ (p_1+c)/(1+\delta\sigma)\}$ be the opt-in threshold of eq. (4). Then every $v\ge v^*_M(p_1)$ satisfies
--   $$2(\kappa_Lv-c)\ \ge\ \kappa_Hv-c\ \ge\ 0.$$
--
--   So every consumer who opts in is in case (i) of eq. (1), and the personalized price of eq. (2) is optimal for her. This is where the first half of Assumption 1 enters the equilibrium.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 15, §3.1, first paragraph

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- §3.1, p. 15: under Assumption 1, every `v ≥ v*_M(p₁)` satisfies `2(κ_L v − c) ≥ κ_H v − c ≥ 0`,
the condition of case (i) of eq. (1). -/
theorem assumption1_case_i (P : Params) (hS : P.Standing) (hA : P.Assumption1) (p1 v : ℝ)
    (hv : vStar P p1 ≤ v) :
    P.kH * v - P.c ≤ 2 * (P.kL * v - P.c) ∧ 0 ≤ P.kH * v - P.c := by sorry

end GDPRDataMarkets.Rights
