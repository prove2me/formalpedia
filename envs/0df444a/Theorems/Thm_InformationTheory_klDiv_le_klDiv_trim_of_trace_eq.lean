-- Prove2me | Theorems.Thm_InformationTheory_klDiv_le_klDiv_trim_of_trace_eq
-- name    : InformationTheory.klDiv_le_klDiv_trim_of_trace_eq
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T15:49:38.207259+00:00
-- url     : https://prove2.me/theorems/ff9463ad-73d3-45d9-a95b-0e1413ae1420
-- title:
--   Relative entropy is unchanged by a refinement with the same trace
-- statement:
--   A refinement of the $\sigma$-algebra that carries no new information where the mass lives does not increase the relative entropy.
--
--   Let $m_1\subseteq m_2$ be $\sigma$-algebras on a set $\Omega$, and let $\mu,\nu$ be finite measures on $(\Omega,m_2)$. Suppose there is a set $S$ carrying all the mass, $\mu(S^{\mathrm c})=\nu(S^{\mathrm c})=0$, on which the two $\sigma$-algebras have the same trace: every $A\in m_2$ satisfies $A\cap S\in m_1$. Then
--
--   $$
--   D\big(\mu\,\|\,\nu\big)_{m_2} \;\le\; D\big(\mu|_{m_1}\,\|\,\nu|_{m_1}\big)_{m_1},
--   $$
--
--   where $\mu|_{m_1}$ denotes the restriction (trim) of $\mu$ to the smaller $\sigma$-algebra.
--
--   Combined with the data-processing inequality, which gives the reverse inequality for any pair of nested $\sigma$-algebras, this is in fact an equality; the direction stated here is the one that is not automatic, and it is what one needs in practice.
--
--   The typical application is to stopped $\sigma$-algebras. On the event $\{\tau\le n\}$ the $\sigma$-algebras $\mathcal F_{\tau\wedge(n+1)}$ and $\mathcal F_{\tau\wedge n}$ have the same trace, because the process has already stopped and no further observation is recorded; this lemma is what turns that informal statement into an inequality between divergences.
--
--   **Formalization Note** The hypothesis is stated as a trace condition on measurable sets rather than as an equality of $\sigma$-algebras, since the two only agree after intersecting with $S$. Measurability of $S$ itself is not assumed: it follows by taking $A$ to be the whole space.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Exercise 14.13 (stopped chain rule, printed p. 197). On the event where the stopping time has already fired, the stopped sigma-algebras agree, and this lemma is the corresponding statement about relative entropy. Compare Theorem 14.1 (density form of relative entropy, printed p. 189).

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem InformationTheory.klDiv_le_klDiv_trim_of_trace_eq {α : Type*}
    {m₁ m₂ : MeasurableSpace α} (h : m₁ ≤ m₂)
    (μ ν : @Measure α m₂) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set α} (hμS : μ Sᶜ = 0) (hνS : ν Sᶜ = 0)
    (htrace : ∀ A, MeasurableSet[m₂] A → MeasurableSet[m₁] (A ∩ S)) :
    @klDiv α m₂ μ ν ≤ @klDiv α m₁ (μ.trim h) (ν.trim h) := by
  sorry
