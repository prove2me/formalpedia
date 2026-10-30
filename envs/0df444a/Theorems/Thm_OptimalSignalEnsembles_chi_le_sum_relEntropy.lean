-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_chi_le_sum_relEntropy
-- name    : OptimalSignalEnsembles.chi_le_sum_relEntropy
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:47.183027+00:00
-- url     : https://prove2.me/theorems/8e37cdc1-5449-4c0f-80a7-4c3f96d80a59
-- title:
--   Eq. (9): $\sum_k p_kD(\rho_k\|\sigma)\ge\chi$, with equality iff $\sigma=\bar\rho$
-- statement:
--   Let $(p_k,\rho_k)_{k=1}^n$ be a finite ensemble of density matrices on $\mathbb C^d$ with average state $\bar\rho$ and Holevo quantity $\chi$. For every density matrix $\sigma$,
--
--   $$\sum_{k=1}^n p_k\, D(\rho_k\,\|\,\sigma) \;\ge\; \chi, \tag{9}$$
--
--   with equality if and only if $\sigma = \bar\rho$.
--
--   Thus $\chi$ is the minimum over all states $\sigma$ of the average relative entropy of the signal states from $\sigma$, attained exactly at the average state; this gives the upper half of the min-max formula (19).
--
--   **Formalization Note** The inequality and the equality are in `EReal` (the left side may be $+\infty$).
--
--   Differences from the source:
--   - encoding: "for any ensemble" of $A$-states → an arbitrary finite ensemble of density matrices; reason: the same instances, as for (4).
--   - encoding: $D$ with values in $[0,\infty]$ → `EReal` with $0\cdot\infty = 0$, $\mathrm{Fin}\,n$ indexing; reason: Lean conventions; same instances.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 4, first bullet, eq. (9), p.5

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble
import Definitions.Def_OptimalSignalEnsembles_holevoChi

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- Eq. (9): for every finite ensemble `(p, ρ)` of density matrices with average state `ρ̄` and
every density matrix `σ`, `∑ₖ pₖ D(ρₖ‖σ) ≥ χ`, with equality if and only if `σ = ρ̄`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 4, first bullet, eq. (9), p.5.

**Formalization Note.** The comparison is in `EReal` (the left side may be `⊤`). -/
theorem chi_le_sum_relEntropy {d : Type} [Fintype d] [DecidableEq d] {n : ℕ}
    (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) (hens : IsEnsemble {σ | IsDensityMatrix σ} p ρ)
    (σ : Matrix d d ℂ) (hσ : IsDensityMatrix σ) :
    (holevoChi p ρ : EReal) ≤ ∑ k, (p k : EReal) * relEntropy (ρ k) σ ∧
      ((holevoChi p ρ : EReal) = ∑ k, (p k : EReal) * relEntropy (ρ k) σ ↔
        σ = avgState p ρ) := by sorry

end OptimalSignalEnsembles
