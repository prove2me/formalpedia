-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_min_max_formula
-- name    : OptimalSignalEnsembles.min_max_formula
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:20:51.26581+00:00
-- url     : https://prove2.me/theorems/fe0259b3-2480-47d5-8f2a-7e9fe2aef1de
-- title:
--   Eq. (19), min-max formula: $\chi^*=\min_\rho\max_{\rho_0\in A}D(\rho_0\|\rho)$
-- statement:
--   Let $A$ be a set of density matrices on the finite-dimensional Hilbert space $\mathbb C^d$, and suppose $(p_k,\rho_k)$ is a $\chi$-optimal ensemble of $A$-states, with average state $\rho^*$. Then
--
--   $$\chi^* \;=\; \min_{\rho}\ \max_{\rho_0 \in A} D(\rho_0\,\|\,\rho), \tag{19}$$
--
--   where the maximum is over all $\rho_0 \in A$ and the minimum is over all average states $\rho$ of finite ensembles of $A$-states. Precisely:
--
--   1. $\chi^* = \inf_{\rho} \sup_{\rho_0\in A} D(\rho_0\|\rho)$, the infimum over average states of ensembles of $A$-states;
--   2. the infimum is attained at $\rho^*$, which is itself such an average state: $\sup_{\rho_0\in A} D(\rho_0\|\rho^*) = \chi^*$;
--   3. the inner supremum at $\rho^*$ is attained: $D(\rho_0\|\rho^*) = \chi^*$ for some $\rho_0 \in A$;
--   4. the same identity holds with the infimum over all density matrices $\sigma$: $\chi^* = \inf_\sigma \sup_{\rho_0\in A} D(\rho_0\|\sigma)$.
--
--   The formula expresses $\chi^*$, for a channel the one-shot classical capacity, as a purely geometric property of the set $A$ — its relative-entropy radius — without reference to any ensemble.
--
--   **Formalization Note** $\chi^*$ is the supremum of $\chi$ in `EReal` and $D$ the published `relEntropy` in `EReal`; min and max are infima and suprema in `EReal`, with attainment stated in clauses 2 and 3. The existence of a $\chi$-optimal ensemble is a hypothesis, as in the paper's standing assumption of Sec. 5; `exists_chiOptimal` supplies one for every nonempty closed $A$.
--
--   Differences from the source:
--   - reading: the formula is stated for "the χ-optimal ensemble" of Sec. 5 → the existence of a $\chi$-optimal ensemble of $A$-states is an explicit hypothesis; reason: it is the standing assumption of Sec. 5 (p.7: "let $\rho_k$ and $p_k$ be the members and probabilities of the ensemble of A-states for which χ takes on its maximum value"); the mission's existence milestone discharges it for every nonempty closed $A$.
--   - reading: $\min_\rho \max_{\rho_0}$ → $\inf$/$\sup$ in `EReal`, with the attainment of the minimum at $\rho^*$ and of the maximum at $\rho^*$ stated as clauses 2 and 3; reason: "min" and "max" assert attainment, which the paper's proof shows at $\rho^*$.
--   - generalization: the minimum over average states of ensembles of $A$-states only → additionally clause 4, the same identity with the minimum over all density matrices; reason: the proof's first half holds "for any state σ" (p.9); clause 1 is the page's formula verbatim.
--   - encoding: finite ensembles over $\mathrm{Fin}\,n$, `EReal` values, natural logarithm; reason: Lean conventions; same instances.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Min-max formula for χ∗, eq. (19), p.9 (proof pp.9–10)

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsChiOptimal
import Definitions.Def_OptimalSignalEnsembles_ensembleAverages

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Min-max formula for χ\***, eq. (19). Let `A` be a set of density matrices on `ℂ^d` and
`(p, ρ)` a χ-optimal ensemble of `A`-states with average state `ρ*`. Then
1. `χ* = min_ρ max_{ρ₀ ∈ A} D(ρ₀‖ρ)`, the minimum over all average states `ρ` of ensembles of
   `A`-states;
2. the minimum is attained at `ρ*`, itself an average state of an ensemble of `A`-states;
3. the inner maximum at `ρ*` is attained: some `ρ₀ ∈ A` has `D(ρ₀‖ρ*) = χ*`;
4. `χ* = min_σ max_{ρ₀ ∈ A} D(ρ₀‖σ)` also with the minimum over all density matrices `σ`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Min-max formula for χ∗, eq. (19), p.9 (proof pp.9–10).

**Formalization Note.** `min`/`max` are `⨅`/`⨆` in `EReal`; their attainment is stated
separately (clauses 2 and 3). The χ-optimal ensemble is a hypothesis, as in the paper's
standing assumption of Sec. 5 (p.7); `exists_chiOptimal` provides one for every nonempty closed
`A`. -/
theorem min_max_formula {d : Type} [Fintype d] [DecidableEq d] (A : Set (Matrix d d ℂ))
    (hA : ∀ σ ∈ A, IsDensityMatrix σ) {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ)
    (hopt : IsChiOptimal A p ρ) :
    chiStar A = (⨅ σ ∈ ensembleAverages A, ⨆ ρ₀ ∈ A, relEntropy ρ₀ σ) ∧
      (avgState p ρ ∈ ensembleAverages A ∧
        (⨆ ρ₀ ∈ A, relEntropy ρ₀ (avgState p ρ)) = chiStar A) ∧
      (∃ ρ₀ ∈ A, relEntropy ρ₀ (avgState p ρ) = chiStar A) ∧
      chiStar A =
        (⨅ σ ∈ {σ : Matrix d d ℂ | IsDensityMatrix σ}, ⨆ ρ₀ ∈ A, relEntropy ρ₀ σ) := by sorry

end OptimalSignalEnsembles
