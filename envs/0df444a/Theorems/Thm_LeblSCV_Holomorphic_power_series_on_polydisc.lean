-- Prove2me | Theorems.Thm_LeblSCV_Holomorphic_power_series_on_polydisc
-- name    : LeblSCV.Holomorphic.power_series_on_polydisc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:12:46.469363+00:00
-- url     : https://prove2.me/theorems/65b2bcb9-b776-42e8-9e4f-c1931e177df7
-- title:
--   Theorem 1.2.1 — holomorphic functions on a polydisc are power series, and conversely
-- statement:
--   Let $\Delta = \Delta_\rho(a) \subset \mathbb{C}^n$ be a polydisc, $\rho_k > 0$ for all $k$.
--
--   1. If $f : \overline{\Delta} \to \mathbb{C}$ is continuous and holomorphic in $\Delta$, then on $\Delta$ the function $f$ equals a power series converging uniformly absolutely on compact subsets of $\Delta$: there are coefficients $c_\alpha \in \mathbb{C}$, $\alpha \in \mathbb{N}_0^n$, such that
--   $$f(z) = \sum_\alpha c_\alpha (z - a)^\alpha \qquad (z \in \Delta), \tag{1.3}$$
--   and $\sum_\alpha |c_\alpha (z-a)^\alpha|$ converges uniformly on every compact $K \subset \Delta$.
--   2. Conversely, if $f : \Delta \to \mathbb{C}$ is defined by (1.3), with the series converging uniformly absolutely on compact subsets of $\Delta$, then $f$ is holomorphic on $\Delta$.
--
--   Holomorphic functions (Definition 1.1.2: locally bounded and holomorphic in each variable separately) are thus exactly the functions given locally by convergent power series.
--
--   **Formalization Note.** Holomorphy is the book's Definition 1.1.2 (`IsHolomorphicOn`), not Mathlib's Fréchet `DifferentiableOn ℂ`, and the conclusion is the book's power-series statement, not Mathlib's `HasFPowerSeriesOnBall` (whose balls for the sup norm on `Fin n → ℂ` are equiradial polydiscs only). Multi-indices are `Fin n → ℕ`; $\overline{\Delta}$ is `closure (polydisc a ρ)`; the sum is unconditional (`HasSum`) and uniform absolute convergence is `ConvergesUniformlyAbsolutelyOn` on each compact subset.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 20, Theorem 1.2.1

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm

namespace LeblSCV.Holomorphic

/-- Theorem 1.2.1 (Lebl, p. 20). Let `Δ = Δ_ρ(a)` be a polydisc (all `ρ_k > 0`).
(1) If `f` is continuous on `closure Δ` and holomorphic in `Δ`, then there are coefficients
`c_α` (`α ∈ ℕ₀ⁿ`) such that the power series `∑_α c_α (z - a)^α` converges uniformly absolutely
on every compact subset of `Δ` and equals `f(z)` at every `z ∈ Δ`.
(2) Conversely, if the power series `∑_α c_α (z - a)^α` converges uniformly absolutely on every
compact subset of `Δ` and `f(z)` is its sum at every `z ∈ Δ`, then `f` is holomorphic on `Δ`. -/
theorem power_series_on_polydisc {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) :
    (∀ f : (Fin n → ℂ) → ℂ, ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)) →
        IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ) →
        ∃ c : (Fin n → ℕ) → ℂ,
          (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) ∧
          ∀ z ∈ LeblSCV.Shared.polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) ∧
    (∀ (c : (Fin n → ℕ) → ℂ) (f : (Fin n → ℂ) → ℂ),
        (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) →
        (∀ z ∈ LeblSCV.Shared.polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) →
        IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ)) := by sorry

end LeblSCV.Holomorphic
