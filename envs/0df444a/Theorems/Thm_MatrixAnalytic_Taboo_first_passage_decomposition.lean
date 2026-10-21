-- Prove2me | Theorems.Thm_MatrixAnalytic_Taboo_first_passage_decomposition
-- name    : MatrixAnalytic.Taboo.first_passage_decomposition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:52.240921+00:00
-- url     : https://prove2.me/theorems/966e8deb-2b4c-40da-aaa5-531a1d00f02b
-- title:
--   Lemma 5.2.4 — $F_{DT} = (I - {}_TF_{DD})^{-1}\,{}_DF_{DT} = {}_TR_{DD}\,{}_DF_{DT}$ and $F_{T^cT} = N_{T^c}P_{T^cT}$
-- statement:
--   Let $\{X_n\}$ be an irreducible, aperiodic Markov chain on a countable state space $S$ with transition matrix $P$, and let $T$ and $D$ be disjoint subsets of $S$. Let $\tau$ be the first passage time to $T$ after time $0$ and
--   $$F_{ij} = \mathrm P[\tau < \infty \;\&\; X_\tau = j \mid X_0 = i]$$
--   the first passage probabilities to $T$; $F_{DT}$ is the matrix of these for $i \in D$, $j \in T$. Let ${}_TF_{DD}$ record the probabilities of returning to $D$ before the first passage to $T$, ${}_TR_{DD}$ the expected numbers of visits to $D$ before the first passage to $T$, and ${}_DF_{DT}$ the probabilities, starting in $D$, of reaching $T$ before returning to $D$, in a given state of $T$. Then
--   $$F_{DT} = (I - {}_TF_{DD})^{-1}\,{}_DF_{DT} = {}_TR_{DD}\,{}_DF_{DT}. \tag{5.25}$$
--   In particular, if $D = T^c$, then
--   $$F_{T^cT} = N_{T^c}P_{T^cT}, \tag{5.26}$$
--   where $N_{T^c}$ is the matrix of expected sojourn times in $T^c$ before the first passage to $T$.
--
--   This gives the distribution of the first state visited in $T$ from a starting point outside $T$, which is the correction term $P_{TT^c}F_{T^cT}$ in the transition matrix of the restricted chain on $T$.
--
--   **Formalization Note** All quantities are probabilities or expected values in $[0, \infty]$ defined by sums over trajectories; $(I - {}_TF_{DD})^{-1}$ is the series $\sum_{\nu \ge 0}({}_TF_{DD})^\nu$ (the book's convention, p. 109). Matrix products sum over the states of $D$ (resp. $T^c$). Aperiodicity is part of the chapter's standing assumption.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 117, Lemma 5.2.4

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

open scoped ENNReal

/-- Latouche & Ramaswami, Lemma 5.2.4 (p. 117). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for any
disjoint subsets `T` and `D`, the matrix `F_{DT}` of first passage probabilities from the states
of `D` to `T` satisfies
(5.25) `F_{DT} = (I − ₜF_{DD})⁻¹ _DF_{DT} = ₜR_{DD} _DF_{DT}`,
where `_DF_{DT}` is `ₜF` with the roles of the sets exchanged (taboo `D`, target `T`); and in
particular, for `D = Tᶜ`,
(5.26) `F_{TᶜT} = N_{Tᶜ} P_{TᶜT}`. -/
theorem first_passage_decomposition {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T D : Set S) (hTD : Disjoint T D) :
    -- (5.25)
    (∀ i ∈ D, ∀ j ∈ T,
      firstPassageF P T i j = ∑' k : D, seriesInv (tabooF P T D) D i k * tabooF P D T k j ∧
      firstPassageF P T i j = ∑' k : D, tabooR P T i k * tabooF P D T k j) ∧
    -- (5.26)
    (∀ i ∉ T, ∀ j ∈ T,
      firstPassageF P T i j = ∑' k : (Tᶜ : Set S), sojournN P Tᶜ i k * ennP P k j) := by sorry

end MatrixAnalytic.Taboo
