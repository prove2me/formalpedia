-- Prove2me | Theorems.Thm_MultitaskContracts_lemma_15
-- name    : MultitaskContracts.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:33:37.569135+00:00
-- url     : https://prove2.me/theorems/e452efeb-85a9-4c51-ad25-33b791e7ed4e
-- title:
--   Lemma 15 — $t_{\mathrm{Sep}}$ is optimal over separable contracts for Min-Pay, Min-Budget and Budgeted Min-Pay
-- statement:
--   Let $I$ be an instance of the multitask model (any dependence) and let $t_{\mathrm{Sep}}(Y)=\sum_{k\in Y}c_k/(p_k-q_k)$ be the separable contract paying $c_k/(p_k-q_k)$ on the success of each task $k$ and nothing on its failure. Then $t_{\mathrm{Sep}}$ is optimal over separable contracts under Min-Pay, under Min-Budget, and under Budgeted Min-Pay for every budget $B\ge\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinBudget}}$. Explicitly:
--   1. $t_{\mathrm{Sep}}$ is separable and implements full effort $K$;
--   2. $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}=\mathbb E_{Y\sim P_K}[t_{\mathrm{Sep}}(Y)]$;
--   3. $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinBudget}}=\max_{Y\subseteq K}t_{\mathrm{Sep}}(Y)$;
--   4. for every budget $B\ge 0$ with $B\ge\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinBudget}}$, $t_{\mathrm{Sep}}(Y)\le B$ for all $Y$ and
--   $$\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{FixedBudget}}(B)=\mathbb E_{Y\sim P_K}[t_{\mathrm{Sep}}(Y)].$$
--
--   In particular $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}=\sum_k p_kc_k/(p_k-q_k)$ is the sum of the stand-alone payments, the separable side of the price of separation.
--
--   Differences from the source:
--   - encoding: "t_Sep is optimal under Min-Pay, Min-Budget, Budgeted Min-Pay" → t_Sep is feasible (separable, implements K), its expected payment equals OPT^Sep_MinPay, its maximum payment equals OPT^Sep_MinBudget, and for B ≥ 0 with B ≥ OPT^Sep_MinBudget it satisfies (BC) and its expected payment equals OPT^Sep_FixedBudget(B); reason: this is what optimality for programs (5)–(7) means; budgets are nonnegative in (5)
--   - encoding: optima with min and ∞ when infeasible → values in ℝ≥0∞ (infima); reason: same values
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Lemma 15, App. C, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_Instance_tSep

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Lemma 15** (Same optimal separable contract for all objectives; App. C, p.55, PDF 57). The
contract `t_Sep` paying `c_k/(p_k − q_k)` on the success of each task `k` and nothing on its
failure is optimal over separable contracts under Min-Pay, under Min-Budget, and under Budgeted
Min-Pay for every budget `B ≥ OPT^Sep_MinBudget`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Lemma 15, p.55.

**Formalization Note.** "Optimal" is spelled out: `t_Sep` is separable and implements `K`; its
expected payment under full effort is `OPT^Sep_MinPay`; its budget `max_Y t_Sep(Y)` is
`OPT^Sep_MinBudget`; and for every budget `B ≥ 0` with `B ≥ OPT^Sep_MinBudget` it satisfies (BC)
and its expected payment is `OPT^Sep_FixedBudget(B)`. Optima are in `ℝ≥0∞`. -/
theorem lemma_15 (I : Instance K) :
    I.tSep ∈ separable K ∧ I.Implements I.tSep Finset.univ ∧
    I.optMinPay (separable K) = ENNReal.ofReal (I.expect Finset.univ I.tSep) ∧
    I.optMinBudget (separable K) =
      ENNReal.ofReal ((Finset.univ : Finset (Finset K)).sup' Finset.univ_nonempty I.tSep) ∧
    ∀ B : ℝ, 0 ≤ B → I.optMinBudget (separable K) ≤ ENNReal.ofReal B →
      (∀ Y, I.tSep Y ≤ B) ∧
        I.optFixedBudget (separable K) B = ENNReal.ofReal (I.expect Finset.univ I.tSep) := by sorry

end MultitaskContracts
