-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_power_four_padding_asymptotics
-- name    : ITPIRPreproc.MatchVec.power_four_padding_asymptotics
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:01.403882+00:00
-- url     : https://prove2.me/theorems/80072711-0873-40f1-bf71-2611ec9df468
-- title:
--   Real asymptotics for power-of-four padding
-- statement:
--   Let \(\eta\to0\), \(A\ge1\), and \(K,c\) be arbitrary. Put \(h(n)=\max(3,\lceil\log_4 n\rceil)\), \(N(n)=4^{h(n)}\), and \(\varepsilon(n)=|\eta(h(n))|\). Then \(\varepsilon\to0\), \(n\le N(n)\le64n\), and there is a fixed \(C\) (depending on \(K,A,c\) only through an explicit uniform constant) for which every component of the padded-adapter budget is bounded by the corresponding target budget with \(C\). The proof uses only elementary real powers: for \(a\in\{0,1/2,1\}\), uniformly bounded \(|\eta(h(n))|\le B\) gives
--   \[
--   N(n)^{a+\eta(h(n))}\le 64^{1+B}n^{a+\varepsilon(n)}.
--   \]
--   The additive \(N(n)\) and \(n^{1/4}\) wrapper terms are absorbed by the \(n^{1+\varepsilon(n)}\) and \(n^{1/2+\varepsilon(n)}\) terms, respectively.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, proof of Theorem 6.1, PDF p.26: the padded length is at most 64n, hence \(o(1)\) exponents remain \(o(1)\); the explicit \(\varepsilon=|\eta(h(n))|\), the bound \(n\le4^{h(n)}\le64n\), and the componentwise inequalities are the formal real-asymptotic argument.

import Definitions.Def_ITPIRPreproc_MatchVec_PowerFourPadding

open scoped ENNReal
open Filter Topology

open ITPIRPreproc.MatchVec

theorem ITPIRPreproc.MatchVec.power_four_padding_asymptotics
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) (K : ℝ) (c : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
        BudgetLE
          (adapterBudget A n (powerFourBudget K c η (padHeight n) lam))
          (targetBudget C c ε n lam) := by sorry
