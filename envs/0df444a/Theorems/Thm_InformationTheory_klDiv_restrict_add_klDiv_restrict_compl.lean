-- Prove2me | Theorems.Thm_InformationTheory_klDiv_restrict_add_klDiv_restrict_compl
-- name    : InformationTheory.klDiv_restrict_add_klDiv_restrict_compl
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T15:38:52.645266+00:00
-- url     : https://prove2.me/theorems/545d9434-8ef4-4757-bf58-00eeb3711ab6
-- title:
--   Additivity of relative entropy over a measurable partition
-- statement:
--   Relative entropy is additive over a measurable partition of the underlying space.
--
--   Let $\mu$ and $\nu$ be finite measures on a measurable space $(\Omega,\mathcal F)$, and let $s\in\mathcal F$. Writing $\mu|_s$ for the restriction of $\mu$ to $s$ and $D(\cdot\,\|\,\cdot)$ for the Kullback-Leibler divergence,
--
--   $$
--   D(\mu\,\|\,\nu) \;=\; D(\mu|_s\,\|\,\nu|_s) \;+\; D(\mu|_{s^{\mathrm c}}\,\|\,\nu|_{s^{\mathrm c}}).
--   $$
--
--   Both sides are equal in $[0,\infty]$: if $\mu$ is not absolutely continuous with respect to $\nu$, or the log-likelihood ratio fails to be integrable, then the failure is inherited by at least one of the two halves and both sides are infinite.
--
--   This is the localisation step used whenever one compares the divergences carried by two nested $\sigma$-algebras that differ only outside a distinguished event: splitting along that event isolates the part where the two $\sigma$-algebras agree from the part where new information arrives. It is the measure-theoretic content behind the stopped chain rule for relative entropy.
--
--   **Formalization Note** The statement is for arbitrary finite measures, not only probability measures. This matters: the restriction of a probability measure to a proper subset is a sub-probability measure, so the additivity can only be stated in a form valid for finite measures. Mathlib's `klDiv` uses the mass-corrected definition $D(\mu\,\|\,\nu)=\int\log\frac{d\mu}{d\nu}\,d\mu+\nu(\Omega)-\mu(\Omega)$, which is precisely the form that makes the identity above hold exactly.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Theorem 14.1 (density form of relative entropy, printed p. 189) for the density formula, and Exercise 14.13 (stopped chain rule, printed p. 197), where additivity over a measurable partition is the localisation step.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory Set
open scoped ENNReal

theorem InformationTheory.klDiv_restrict_add_klDiv_restrict_compl {α : Type*}
    {mα : MeasurableSpace α} (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  sorry
