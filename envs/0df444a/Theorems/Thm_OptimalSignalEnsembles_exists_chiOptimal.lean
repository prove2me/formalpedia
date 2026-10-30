-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_exists_chiOptimal
-- name    : OptimalSignalEnsembles.exists_chiOptimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:21:00.172959+00:00
-- url     : https://prove2.me/theorems/c30a4b2d-0263-4dae-8a0b-f7fc83babf90
-- title:
--   Existence: every nonempty closed set of states has a $\chi$-optimal ensemble
-- statement:
--   Let $A$ be a nonempty closed set of density matrices on the finite-dimensional Hilbert space $\mathbb C^d$. Then there is a finite ensemble $(p_k,\rho_k)$ of $A$-states that is $\chi$-optimal:
--
--   $$\chi(p,\rho) = \chi^*(A).$$
--
--   In particular $\chi^*(A)$ is a finite maximum. The paper states this for the set of outputs of a noisy channel on a finite-dimensional space, which is nonempty, convex and compact; this statement needs neither convexity nor compact extreme points. It discharges the standing hypothesis of Sec. 5 — that a $\chi$-optimal ensemble exists — on which the maximal distance property, the equal distance property and the min-max formula are stated.
--
--   **Formalization Note** $A$ carries the entrywise topology of $M_d(\mathbb C)$; since density matrices form a bounded set, closed and compact coincide here.
--
--   Differences from the source:
--   - generalization: $A$ the set of outputs of a noisy channel on a finite-dimensional Hilbert space → $A$ any nonempty closed set of density matrices; reason: a channel's output set is the continuous image of the compact set of input states, hence nonempty and compact, so closed; the Lean statement specializes to the page's.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 5, Existence, pp.7–8

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsChiOptimal

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Existence of a χ-optimal ensemble.** On a finite-dimensional Hilbert space `ℂ^d`, every
nonempty closed set `A` of density matrices has a χ-optimal finite ensemble of `A`-states.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 5, "Existence", pp.7–8 (stated there for `A` the set of outputs of a noisy channel,
which is nonempty, convex and compact, hence closed).

**Formalization Note.** `A` carries the subspace topology of `Matrix d d ℂ` (entrywise); since
`A` is bounded, closed is the same as compact. Convexity is not assumed. -/
theorem exists_chiOptimal {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ))
    (hA : ∀ σ ∈ A, IsDensityMatrix σ) (hne : A.Nonempty) (hclosed : IsClosed A) :
    ∃ (n : ℕ) (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ), IsChiOptimal A p ρ := by sorry

end OptimalSignalEnsembles
