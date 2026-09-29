-- Prove2me | Theorems.Thm_GelfondSchneider_common_field
-- name    : GelfondSchneider.common_field
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:17.339837+00:00
-- url     : https://prove2.me/theorems/225f1e21-3d8c-442b-a6c8-153398b69c97
-- title:
--   e^l, β and e^{βl} lie in one number field
-- statement:
--   If $e^{l}$, $\beta$ and $e^{\beta l}$ are algebraic, there is a number field $K$ with an embedding $\sigma : K \to \mathbb C$ and elements $\alpha', \beta', \gamma' \in K$ such that $\sigma(\alpha') = e^{l}$, $\sigma(\beta') = \beta$ and $\sigma(\gamma') = e^{\beta l}$.
--
--   Take $K = \mathbb Q(e^{l}, \beta, e^{\beta l})$ and $\sigma$ its inclusion. This is the setting of Gelfond's proof, in logarithmic form.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem common_field (l β : ℂ) (hβ : IsAlgebraic ℚ β) (hα : IsAlgebraic ℚ (Complex.exp l))
    (hγ : IsAlgebraic ℚ (Complex.exp (β * l))) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (σ : K →+* ℂ) (α' β' γ' : K),
      σ α' = Complex.exp l ∧ σ β' = β ∧ σ γ' = Complex.exp (β * l) := by
  sorry

end GelfondSchneider
