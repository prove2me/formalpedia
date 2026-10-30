-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_maximal_distance
-- name    : OptimalSignalEnsembles.maximal_distance
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:20:49.665078+00:00
-- url     : https://prove2.me/theorems/c5b1840e-d32f-4256-b59a-735fbb709263
-- title:
--   Eq. (17), maximal distance property: $D(\rho_0\|\rho^*)\le\chi^*$ for $\rho_0\in A$
-- statement:
--   Let $A$ be a set of density matrices on $\mathbb C^d$ and let $(p_k,\rho_k)$ be a $\chi$-optimal ensemble of $A$-states with average state $\rho^*$. Then for every state $\rho_0 \in A$,
--
--   $$D(\rho_0\,\|\,\rho^*) \;\le\; \chi^*. \tag{17}$$
--
--   In particular $D(\rho_0\|\rho^*)$ is finite, so $\operatorname{supp}\rho_0 \subseteq \operatorname{supp}\rho^*$ for all $\rho_0 \in A$ (the maximal support property). Every available state lies within relative-entropy distance $\chi^*$ of the optimal average state.
--
--   **Formalization Note** The inequality is in `EReal`; $\chi^*(A)$ is finite because the optimal ensemble attains it.
--
--   Differences from the source:
--   - encoding: $\chi^*$ "the maximum of $\chi$" and $D \in [0,\infty]$ → $\chi^*$ the supremum in `EReal`, attained by the hypothesis, and $D$ in `EReal`; reason: Lean convention; for a $\chi$-optimal ensemble the supremum is the maximum.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 5, Maximal distance property, eq. (17), p.8

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsChiOptimal

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Maximal distance property**, eq. (17): let `A` be a set of density matrices and `(p, ρ)` a
χ-optimal ensemble of `A`-states with average state `ρ*`. Then `D(ρ₀‖ρ*) ≤ χ*` for every
`ρ₀ ∈ A`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 5, "Maximal distance property", eq. (17), p.8.

**Formalization Note.** The inequality is in `EReal`; since `χ*` is finite for an optimal
ensemble, it includes `D(ρ₀‖ρ*) < ⊤`, i.e. `supp ρ₀ ⊆ supp ρ*` (the proof's infinite case). -/
theorem maximal_distance {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ))
    (hA : ∀ σ ∈ A, IsDensityMatrix σ) {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ)
    (hopt : IsChiOptimal A p ρ) :
    ∀ ρ₀ ∈ A, relEntropy ρ₀ (avgState p ρ) ≤ chiStar A := by sorry

end OptimalSignalEnsembles
