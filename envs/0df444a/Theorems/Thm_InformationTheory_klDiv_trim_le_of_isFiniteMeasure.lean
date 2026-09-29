-- Prove2me | Theorems.Thm_InformationTheory_klDiv_trim_le_of_isFiniteMeasure
-- name    : InformationTheory.klDiv_trim_le_of_isFiniteMeasure
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:00:21.195257+00:00
-- url     : https://prove2.me/theorems/dfda1e34-7741-4292-a4e0-a52173a400e2
-- title:
--   Data-processing inequality for relative entropy (finite measures)
-- statement:
--   The data-processing inequality for relative entropy, for finite measures: coarsening the $\sigma$-algebra cannot increase the divergence.
--
--   Let $m\subseteq m_0$ be $\sigma$-algebras on a set $\Omega$ and let $\mu,\nu$ be finite measures on $(\Omega,m_0)$. Writing $\mu|_m$ for the restriction of $\mu$ to the smaller $\sigma$-algebra,
--
--   $$
--   D\big(\mu|_m\,\|\,\nu|_m\big) \;\le\; D\big(\mu\,\|\,\nu\big).
--   $$
--
--   Observing a coarser function of the data can only make two hypotheses harder to tell apart.
--
--   The corresponding statement for probability measures is standard. The extension to finite measures recorded here is what one needs as soon as the underlying space is split along an event: restricting a probability measure to a proper subset leaves a sub-probability measure, so any argument that localises to an event immediately leaves the probability-measure setting.
--
--   **Formalization Note** Mathlib's `klDiv` uses the mass-corrected definition $D(\mu\|\nu)=\int\log\frac{d\mu}{d\nu}\,d\mu+\nu(\Omega)-\mu(\Omega)$, which is the form for which this statement is true for finite, and not merely probability, measures.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Exercise 14.10 (data processing inequality), printed p. 196; see also Theorem 14.1 (density form of relative entropy), printed p. 189.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem InformationTheory.klDiv_trim_le_of_isFiniteMeasure {α : Type*}
    {m m₀ : MeasurableSpace α} (hm : m ≤ m₀) (μ ν : @Measure α m₀)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    @klDiv α m (μ.trim hm) (ν.trim hm) ≤ @klDiv α m₀ μ ν := by
  sorry
