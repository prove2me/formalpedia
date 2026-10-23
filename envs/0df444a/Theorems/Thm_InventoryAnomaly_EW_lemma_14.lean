-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_14
-- name    : InventoryAnomaly.EW.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:58.018831+00:00
-- url     : https://prove2.me/theorems/3c56bf3c-d53e-488b-8c3a-dd7450cffbf7
-- title:
--   Lemma 14, p. 41 — Bernstein bound for the sum of [0,1]-valued variables over a Bernoulli(p_O) sample Ω
-- statement:
--   Let $O_{ij}\in\{0,1\}$, $(i,j)\in[n]\times[m]$, be i.i.d. $\mathrm{Ber}(p_O)$ variables, $\Omega=\{(i,j):O_{ij}=1\}$, and let $T_{ij}\in[0,1]$ be independent random variables with $\mathbb E\,T_{ij}=p_{ij}$. Put $S=\sum_{(i,j)}p_Op_{ij}$. There is a universal constant $C$ such that, with probability at least $1-1/(nm)$,
--   $$\Big|\sum_{(i,j)\in\Omega}T_{ij}-S\Big|\le C\Big(\sqrt{S\log(mn)}+\log(mn)\Big).$$
--
--   This concentration inequality is used to control $|\Omega|$ (with $T_{ij}=1$) and the empirical CDF counts $|\{(i,j)\in\Omega:X_{ij}\le t\}|$ in the analysis of the moment-matching estimator.
--
--   **Formalization Note.** $\sum_{(i,j)\in\Omega}T_{ij}$ is written $\sum_{ij}O_{ij}T_{ij}$. The family $(O_{ij})\cup(T_{ij})$ is assumed jointly independent (the proof uses independence of the products $T_{ij}O_{ij}$). Only the first display of the lemma is formalized; its "in particular" clause hides an unnamed threshold $S\gtrsim\log(nm)$. $n,m\ge1$.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 41, Lemma 14

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_14 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n m : ℕ}
      (pO : ℝ) (O T : Fin n × Fin m → Ω → ℝ) (p : Fin n × Fin m → ℝ),
      0 < n → 0 < m → 0 ≤ pO → pO ≤ 1 →
      (∀ ij, Measurable (O ij)) → (∀ ij, Measurable (T ij)) →
      iIndepFun (fun k : (Fin n × Fin m) ⊕ (Fin n × Fin m) => Sum.elim O T k) P →
      (∀ ij ω, O ij ω = 0 ∨ O ij ω = 1) → (∀ ij, P.real {ω | O ij ω = 1} = pO) →
      (∀ ij ω, 0 ≤ T ij ω ∧ T ij ω ≤ 1) → (∀ ij, ∫ ω, T ij ω ∂P = p ij) →
      1 - 1 / ((n : ℝ) * m) ≤ P.real {ω | |∑ ij, O ij ω * T ij ω - ∑ ij, pO * p ij| ≤
        C * (Real.sqrt ((∑ ij, pO * p ij) * Real.log (m * n)) + Real.log (m * n))} := by sorry

end InventoryAnomaly.EW
