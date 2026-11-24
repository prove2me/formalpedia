-- Prove2me | Theorems.Thm_LatitudeMaximizer
-- name    : LatitudeMaximizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:58:39.218792+00:00
-- url     : https://prove2.me/theorems/8267ff75-36a4-4404-b3b7-a409eb21a748
-- title:
--   Latitude Maximizer: Latitude Maximizer
-- statement:
--   A continuous function attains a maximum on the latitude set
--   `{v : ‖v‖ = 1, ⟪e,v⟫ = 0}`. This is the maximizer `v₀` that
--   `TangentialLaplacianBound` takes as a hypothesis; the latitude set is a proper
--   closed subset of the unit sphere and its nonemptiness needs `2 ≤ n`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LatitudeMaximizer.lean#L11-L45
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LatitudeMaximizer.lean#L11-L45

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_LatitudeMaximizer
set_option autoImplicit false
@[expose] public section
public section

theorem LatitudeMaximizer {n : ℕ} (hn : 2 ≤ n) {e : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    ∃ v₀ : EuclideanSpace ℝ (Fin n), ‖v₀‖ = 1 ∧ inner ℝ e v₀ = (0 : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) → f v ≤ f v₀ := by sorry
