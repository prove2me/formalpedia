-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_equal_distance
-- name    : OptimalSignalEnsembles.equal_distance
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:20:37.075+00:00
-- url     : https://prove2.me/theorems/9beb9749-4a04-48f6-a380-42f7c2b7a3e4
-- title:
--   Eq. (18), equal distance property: $D(\rho_k\|\rho^*)=\chi^*$ when $p_k\ne0$
-- statement:
--   Let $A$ be a set of density matrices on $\mathbb C^d$ and let $(p_k,\rho_k)$ be a $\chi$-optimal ensemble of $A$-states with average state $\rho^*$. If $\rho_k$ is a member with $p_k \ne 0$, then
--
--   $$D(\rho_k\,\|\,\rho^*) \;=\; \chi^*. \tag{18}$$
--
--   All members of nonzero weight of an optimal ensemble are at the same relative-entropy distance from the optimal average state; with (17) this shows that the inner maximum of the min-max formula is attained at $\rho^*$.
--
--   **Formalization Note** The equality is in `EReal`.
--
--   Differences from the source:
--   - encoding: $\chi^*$ "the maximum of $\chi$" → the supremum in `EReal`, attained by the hypothesis; members indexed by $\mathrm{Fin}\,n$; reason: Lean convention; same instances.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 5, Equal distance property, eq. (18), p.9

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsChiOptimal

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Equal distance property**, eq. (18): let `A` be a set of density matrices and `(p, ρ)` a
χ-optimal ensemble of `A`-states with average state `ρ*`. Every member `ρₖ` with `pₖ ≠ 0`
satisfies `D(ρₖ‖ρ*) = χ*`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 5, "Equal distance property", eq. (18), p.9.

**Formalization Note.** The equality is in `EReal`. -/
theorem equal_distance {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ))
    (hA : ∀ σ ∈ A, IsDensityMatrix σ) {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ)
    (hopt : IsChiOptimal A p ρ) (k : Fin n) (hk : p k ≠ 0) :
    relEntropy (ρ k) (avgState p ρ) = chiStar A := by sorry

end OptimalSignalEnsembles
