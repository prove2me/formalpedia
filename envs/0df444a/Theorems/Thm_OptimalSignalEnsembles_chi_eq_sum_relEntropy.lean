-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_chi_eq_sum_relEntropy
-- name    : OptimalSignalEnsembles.chi_eq_sum_relEntropy
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:41.013003+00:00
-- url     : https://prove2.me/theorems/f191ccd3-0444-4d22-a69c-7d1081c24bb0
-- title:
--   Eq. (4): $\chi=\sum_k p_k D(\rho_k\|\bar\rho)$
-- statement:
--   Let $(p_k,\rho_k)_{k=1}^n$ be a finite ensemble of density matrices on $\mathbb C^d$ with average state $\bar\rho = \sum_k p_k\rho_k$ and Holevo quantity $\chi$. Then
--
--   $$\chi \;=\; \sum_{k=1}^n p_k\, D(\rho_k\,\|\,\bar\rho), \tag{4}$$
--
--   where $D(\rho\|\sigma) = \operatorname{Tr}\rho\log\rho - \operatorname{Tr}\rho\log\sigma$ if $\operatorname{supp}\rho \subseteq \operatorname{supp}\sigma$ and $D(\rho\|\sigma) = +\infty$ otherwise.
--
--   So $\chi$ is the average relative-entropy "distance" of the signal states from the average state; this is the form of $\chi$ on which the geometric results of the paper rest.
--
--   **Formalization Note** The identity is in `EReal`. A member with $p_k = 0$ may have $D(\rho_k\|\bar\rho) = +\infty$; `EReal` has $0\cdot(+\infty) = 0$, so it contributes nothing, as on the page.
--
--   Differences from the source:
--   - encoding: an ensemble of signal states in the available set $A$ → an arbitrary finite ensemble of density matrices; reason: every finite ensemble of density matrices is an ensemble of $A$-states for $A$ the set of its members, and conversely, so the instances are the same.
--   - encoding: $D$ with values in $[0,\infty]$ and members of zero weight absent → `EReal` values with $0\cdot\infty = 0$, members indexed by $\mathrm{Fin}\,n$ with zero weights allowed; reason: Lean conventions; a zero-weight member contributes $0$, as if absent.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, eq. (4), p.3

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble
import Definitions.Def_OptimalSignalEnsembles_holevoChi

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **χ as an average relative entropy**, eq. (4): for every finite ensemble `(p, ρ)` of
density matrices with average state `ρ̄`, `χ = ∑ₖ pₖ D(ρₖ‖ρ̄)`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, eq. (4), p.3.

**Formalization Note.** `D` is the published `relEntropy`, valued in `EReal` and `⊤` unless
`supp ρₖ ⊆ supp ρ̄`. A member with `pₖ = 0` may have `D(ρₖ‖ρ̄) = ⊤`; `EReal` has `0 * ⊤ = 0`,
so such a member contributes nothing, as on the page. -/
theorem chi_eq_sum_relEntropy {d : Type} [Fintype d] [DecidableEq d] {n : ℕ}
    (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) (hens : IsEnsemble {σ | IsDensityMatrix σ} p ρ) :
    (holevoChi p ρ : EReal) = ∑ k, (p k : EReal) * relEntropy (ρ k) (avgState p ρ) := by sorry

end OptimalSignalEnsembles
