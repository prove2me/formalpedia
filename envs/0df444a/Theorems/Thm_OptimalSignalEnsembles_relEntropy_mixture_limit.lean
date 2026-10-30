-- Prove2me | Theorems.Thm_OptimalSignalEnsembles_relEntropy_mixture_limit
-- name    : OptimalSignalEnsembles.relEntropy_mixture_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:12.21727+00:00
-- url     : https://prove2.me/theorems/f4e84a04-8e7f-4f3b-9f6a-cc36b4edb075
-- title:
--   Sec. 4: $D(\rho_0\|(1-\eta)\rho+\eta\rho_0)$ is finite and its limit as $\eta\to0$
-- statement:
--   Let $\rho_0$ and $\rho$ be density matrices on $\mathbb C^d$ and $\rho' = (1-\eta)\rho + \eta\rho_0$. Then
--
--   1. $D(\rho_0\,\|\,\rho')$ exists and is finite for $0 < \eta \le 1$;
--   2. if $\operatorname{supp}\rho_0 \subseteq \operatorname{supp}\rho$, then $D(\rho_0\,\|\,\rho') \to D(\rho_0\,\|\,\rho)$ as $\eta \to 0$;
--   3. otherwise, $D(\rho_0\,\|\,\rho') \to \infty$ as $\eta \to 0$.
--
--   Together with (14) this lets one choose $\eta$ small enough that $D(\rho_0\|\rho')$ is close to (or, in the infinite case, larger than any bound) $D(\rho_0\|\rho)$, which is how the maximal distance property is proved.
--
--   **Formalization Note** $D$ takes values in `EReal`; "finite" is $\ne +\infty$. The support condition is the published `SupportLE` ($\ker\rho \subseteq \ker\rho_0$). The limit $\eta \to 0$ is taken from the right, and "$\to\infty$" is convergence to $+\infty$ in `EReal`.
--
--   Differences from the source:
--   - encoding: $\eta \to 0$ → the right limit $\eta \to 0^+$; $\to \infty$ → convergence to $\top$ in `EReal`; reason: $\rho'$ is a state only for $\eta \ge 0$, and the paper considers $0 < \eta \le 1$.
--   - encoding: $\log$ of unstated base (the paper counts $\chi$ in bits) on a finite-dimensional Hilbert space → the natural logarithm, operators `Matrix d d ℂ` for a finite type `d : Type`; reason: $S$, $D$, $\chi$ and $\chi^*$ all scale by the same positive factor under a change of base, so the statement holds in one base iff in every base; every finite-dimensional Hilbert space is $\mathbb C^d$.
-- source:
--   Schumacher–Westmoreland, Optimal signal ensembles, arXiv:quant-ph/9912122v1, Sec. 4, last paragraph, p.7

import Mathlib
import Definitions.Def_pme_quantum_basics

open ProjectiveMeasurementEquilibration
open Filter Topology

namespace OptimalSignalEnsembles

/-- **The `η → 0` limits**, Sec. 4, last paragraph. Let `ρ₀`, `ρ` be density matrices and
`ρ′(η) = (1 − η)ρ + ηρ₀`. Then
1. `D(ρ₀‖ρ′(η))` is finite for `0 < η ≤ 1`;
2. if `supp ρ₀ ⊆ supp ρ`, then `D(ρ₀‖ρ′(η)) → D(ρ₀‖ρ)` as `η → 0`;
3. otherwise `D(ρ₀‖ρ′(η)) → ∞` as `η → 0`.

Schumacher–Westmoreland, *Optimal signal ensembles*, arXiv:quant-ph/9912122v1, Sec. 4, last paragraph, p.7.

**Formalization Note.** `D` is the published `relEntropy` in `EReal`; "finite" is `≠ ⊤`
(`relEntropy` never takes the value `⊥`). `supp ρ₀ ⊆ supp ρ` is the published `SupportLE ρ₀ ρ`
(`ker ρ ⊆ ker ρ₀`). `η → 0` is the right limit `𝓝[>] 0` (only `η > 0` is meaningful), and
`→ ∞` is convergence to `⊤` in `EReal`. -/
theorem relEntropy_mixture_limit {d : Type} [Fintype d] [DecidableEq d]
    (ρ₀ ρ : Matrix d d ℂ) (hρ₀ : IsDensityMatrix ρ₀) (hρ : IsDensityMatrix ρ) :
    (∀ η : ℝ, 0 < η → η ≤ 1 →
        relEntropy ρ₀ (((1 - η : ℝ) : ℂ) • ρ + ((η : ℝ) : ℂ) • ρ₀) ≠ ⊤) ∧
      (SupportLE ρ₀ ρ →
        Tendsto (fun η : ℝ => relEntropy ρ₀ (((1 - η : ℝ) : ℂ) • ρ + ((η : ℝ) : ℂ) • ρ₀))
          (𝓝[>] 0) (𝓝 (relEntropy ρ₀ ρ))) ∧
      (¬ SupportLE ρ₀ ρ →
        Tendsto (fun η : ℝ => relEntropy ρ₀ (((1 - η : ℝ) : ℂ) • ρ + ((η : ℝ) : ℂ) • ρ₀))
          (𝓝[>] 0) (𝓝 ⊤)) := by sorry

end OptimalSignalEnsembles
