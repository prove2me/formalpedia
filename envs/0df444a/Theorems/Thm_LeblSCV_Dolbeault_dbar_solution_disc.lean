-- Prove2me | Theorems.Thm_LeblSCV_Dolbeault_dbar_solution_disc
-- name    : LeblSCV.Dolbeault.dbar_solution_disc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T20:18:31.133757+00:00
-- url     : https://prove2.me/theorems/7f8480d1-0b4c-4b7c-b61f-4a2cf74c930c
-- title:
--   Lemma 4.4.6 — solving ∂ψ/∂z̄ = g on a disc (restricted to discs)
-- statement:
--   Let $U = \{\zeta\in\mathbb{C} : |\zeta - c| < r\}$ be an open disc, $r > 0$, and let $g$ be smooth on an open neighbourhood of $\overline{U}$. Define $\psi : U \to \mathbb{C}$ by
--   $$\psi(z) = \frac{1}{2\pi i}\int_U \frac{g(\zeta)}{\zeta - z}\, d\zeta\wedge d\bar\zeta .$$
--   Then the integral converges for every $z\in U$, $\psi$ is smooth on $U$, and $\dfrac{\partial\psi}{\partial\bar z} = g$ on $U$. This is the one-variable $\bar\partial$-problem, solved by the Cauchy transform; the Dolbeault–Grothendieck lemma applies it one variable at a time, with the others as parameters.
--
--   **Formalization Note.** $d\zeta \wedge d\bar\zeta = -2i\, dA$ with $dA$ the Lebesgue measure on $\mathbb{C}$ (Mathlib's `volume`), so the integral is `(2πi)⁻¹ * ((-2i) * ∫ ζ in U, g ζ / (ζ - z))`. The conclusion also records that the integrand is integrable on $U$ for each $z\in U$ (asserted in the book's proof, p. 142), so the Bochner integral is the genuine one. **Restriction:** the book allows any bounded open $U\subset\mathbb{C}$ with piecewise-$C^1$ boundary; this item states the case of a disc, which is the case the proof of Lemma 4.4.7 uses. $\psi$ is any function equal to the integral on $U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 141, Lemma 4.4.6

import Mathlib
import Definitions.Def_LeblSCV_Shared_dbar

open Complex MeasureTheory
open scoped Real
open scoped ContDiff

namespace LeblSCV.Dolbeault

/-- Lemma 4.4.6 (Lebl, p. 141), for `U` an open disc `{|ζ - c| < r}`, `r > 0` (restriction: the book
allows any bounded open `U ⊆ ℂ` with piecewise-`C¹` boundary). Let `g` be smooth on an open
neighborhood `V` of the closed disc `Ū`. Define `ψ : U → ℂ` by
`ψ(z) = (1/2πi) ∫_U g(ζ)/(ζ - z) dζ ∧ dζ̄`, with `dζ ∧ dζ̄ = (-2i) dA`, `dA` the Lebesgue area
measure on `ℂ`. Then for every `z ∈ U` the integrand is integrable on `U` (as the proof on p. 142
notes), `ψ` is smooth on `U`, and `∂ψ/∂z̄ = g` on `U`. (`ψ` is prescribed only on `U`;
its values off `U` do not enter the conclusion, because `U` is open.) -/
theorem dbar_solution_disc {c : ℂ} {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∃ V : Set ℂ, IsOpen V ∧ Metric.closedBall c r ⊆ V ∧ ContDiffOn ℝ ∞ g V)
    (ψ : ℂ → ℂ)
    (hψ : ∀ z ∈ Metric.ball c r,
      ψ z = (2 * π * I)⁻¹ * ((-2 * I) * ∫ ζ in Metric.ball c r, g ζ / (ζ - z))) :
    (∀ z ∈ Metric.ball c r, IntegrableOn (fun ζ : ℂ => g ζ / (ζ - z)) (Metric.ball c r)) ∧
      ContDiffOn ℝ ∞ ψ (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, LeblSCV.Shared.dbar ψ z = g z := by sorry

end LeblSCV.Dolbeault
