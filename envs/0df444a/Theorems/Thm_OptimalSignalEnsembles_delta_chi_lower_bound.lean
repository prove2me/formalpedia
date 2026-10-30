-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_delta_chi_lower_bound
-- name    : OptimalSignalEnsembles.delta_chi_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:41.706104+00:00
-- url     : https://prove2.me/theorems/6aaee441-d060-4727-85e2-5e2279569daf
-- title:
--   Eq. (14): $\Delta\chi\ge\eta\,(D(\rho_0\|\rho')-\chi)$
-- statement:
--   Let $(p_k,\rho_k)_{k=1}^n$ be a finite ensemble of density matrices on $\mathbb C^d$ with average state $\bar\rho$ and Holevo quantity $\chi$, let $\rho_0$ be a density matrix and $0 \le \eta \le 1$. The **modified ensemble** consists of the states $\rho_0, \rho_1, \dots, \rho_n$ with probabilities $\eta, (1-\eta)p_1, \dots, (1-\eta)p_n$; its average state is
--
--   $$\rho' = (1-\eta)\bar\rho + \eta\rho_0 \tag{11}$$
--
--   and its Holevo quantity is $\chi'$. Then $\Delta\chi = \chi' - \chi$ satisfies
--
--   $$\Delta\chi \;\ge\; \eta\,\big(D(\rho_0\,\|\,\rho') - \chi\big). \tag{14}$$
--
--   This lower bound shows that adding a state that is far from the modified average increases $\chi$; it is the step that yields the maximal distance property (17).
--
--   **Formalization Note** The modified ensemble is indexed by $\mathrm{Fin}(n+1)$ with $\rho_0$ at index $0$. The inequality is in `EReal`; for $\eta > 0$ it implies $D(\rho_0\|\rho') < \infty$. At $\eta = 0$ both sides are $0$.
--
--   Differences from the source:
--   - generalization: "a new state $\rho_0$ with probability $\eta$", $0 < \eta \le 1$ (the range of p.7) → $0 \le \eta \le 1$, the endpoint $\eta = 0$ included; reason: at $\eta = 0$ the modified ensemble has the same $\chi$ and the right side is $0\cdot(D - \chi) = 0$ in `EReal`, so the Lean statement adds one true instance and specializes to the page's for $0 < \eta \le 1$.
--   - encoding: $\chi'$ defined by (13) as $(1-\eta)\sum_k p_k D(\rho_k\|\rho') + \eta D(\rho_0\|\rho')$ → $\chi'$ the Holevo quantity (1) of the modified ensemble; reason: the two agree by (4), which the page uses to write (12)–(13).
--   - encoding: an ensemble of $A$-states → an arbitrary finite ensemble of density matrices, $\rho_0$ any state; reason: Sec. 4 does not use $A$ in this computation; same instances.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, eqs. (11)–(14), p.6

import Mathlib
import Definitions.Def_pme_quantum_basics
import Definitions.Def_OptimalSignalEnsembles_IsEnsemble
import Definitions.Def_OptimalSignalEnsembles_holevoChi

open ProjectiveMeasurementEquilibration

namespace OptimalSignalEnsembles

/-- **Lower bound on `Δχ`**, eq. (14). Let `(p, ρ)` be a finite ensemble of density matrices with
average state `ρ̄` and Holevo quantity `χ`, let `ρ₀` be a density matrix and `0 ≤ η ≤ 1`. The
*modified ensemble* has members `ρ₀, ρ₁, …, ρₙ` with weights `η, (1 − η)p₁, …, (1 − η)pₙ`; its
average state is `ρ′ = (1 − η)ρ̄ + ηρ₀` (11) and its Holevo quantity is `χ′`. Then
`Δχ = χ′ − χ ≥ η (D(ρ₀‖ρ′) − χ)`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, eqs. (11)–(14), p.6.

**Formalization Note.** The modified ensemble is indexed by `Fin (n + 1)`, the new member `ρ₀`
at index `0` (`Fin.cons`). The inequality is in `EReal`; for `η > 0` it forces
`D(ρ₀‖ρ′) < ⊤`. At `η = 0` both sides are `0` (`EReal` has `0 * ⊤ = 0`), so the endpoint is
included. -/
theorem delta_chi_lower_bound {d : Type} [Fintype d] [DecidableEq d] {n : ℕ}
    (p : Fin n → ℝ) (ρ : Fin n → Matrix d d ℂ) (hens : IsEnsemble {σ | IsDensityMatrix σ} p ρ)
    (ρ₀ : Matrix d d ℂ) (hρ₀ : IsDensityMatrix ρ₀) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (η : EReal) * (relEntropy ρ₀ (((1 - η : ℝ) : ℂ) • avgState p ρ + ((η : ℝ) : ℂ) • ρ₀) -
        (holevoChi p ρ : EReal)) ≤
      ((holevoChi (Fin.cons η (fun k => (1 - η) * p k) : Fin (n + 1) → ℝ)
          (Fin.cons ρ₀ ρ : Fin (n + 1) → Matrix d d ℂ) - holevoChi p ρ : ℝ) : EReal) := by sorry

end OptimalSignalEnsembles
