-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_donald_identity
-- name    : OptimalSignalEnsembles.donald_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:41.688745+00:00
-- url     : https://prove2.me/theorems/43241c7e-81ed-4e66-8e9a-0ddc71271277
-- title:
--   Eq. (8), Donald's identity: $\sum_k p_kD(\rho_k\|\sigma)=\chi+D(\bar\rho\|\sigma)$
-- statement:
--   Let $(p_k,\rho_k)_{k=1}^n$ be a finite ensemble of density matrices on $\mathbb C^d$ with average state $\bar\rho$ and Holevo quantity $\chi$, and let $\sigma$ be any density matrix (the "alternate" state). Then
--
--   $$\sum_{k=1}^n p_k\, D(\rho_k\,\|\,\sigma) \;=\; \chi + D(\bar\rho\,\|\,\sigma). \tag{8}$$
--
--   Both sides may be $+\infty$. This identity, due to Donald, is the tool behind every estimate of the paper: (9), (10), and the bounds (14), (15) on the change of $\chi$ when the ensemble is modified.
--
--   **Formalization Note** $D$ is the published `relEntropy` with values in `EReal` ($+\infty$ unless $\operatorname{supp}\rho \subseteq \operatorname{supp}\sigma$); members of zero weight contribute $0\cdot D = 0$.
--
--   Differences from the source:
--   - encoding: an ensemble of signal states $\rho_k \in A$ → an arbitrary finite ensemble of density matrices; reason: every such ensemble is an ensemble of $A$-states for $A$ its set of members, and conversely.
--   - encoding: $D$ with values in $[0,\infty]$, zero-weight members absent → `EReal` with $0\cdot\infty = 0$, $\mathrm{Fin}\,n$ indexing; reason: Lean conventions; same instances.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, eq. (8), p.5

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble
import Definitions.Def_OptimalSignalEnsembles_holevoChi

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Donald's identity**, eq. (8): for every finite ensemble `(p, ρ)` of density matrices with
average state `ρ̄` and every density matrix `σ`,
`∑ₖ pₖ D(ρₖ‖σ) = χ + D(ρ̄‖σ)`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, eq. (8), p.5.

**Formalization Note.** Both sides are in `EReal` and may equal `⊤` (when some member of positive
weight is not supported in `supp σ`); `0 * ⊤ = 0` for members of zero weight. -/
theorem donald_identity {d : Type} [Fintype d] [DecidableEq d] {n : ℕ}
    (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) (hens : IsEnsemble {σ | IsDensityMatrix σ} p ρ)
    (σ : Matrix d d ℂ) (hσ : IsDensityMatrix σ) :
    ∑ k, (p k : EReal) * relEntropy (ρ k) σ =
      (holevoChi p ρ : EReal) + relEntropy (avgState p ρ) σ := by sorry

end OptimalSignalEnsembles
