-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_general_case_of_special_case
-- name    : HartSchmeidler.Compact.general_case_of_special_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:37.31631+00:00
-- url     : https://prove2.me/theorems/42f05664-882f-4ac8-a9c3-5bd9433a4c69
-- title:
--   Proof of Theorem 3, p. 25 — the general case: (4) for every Borel deviation follows from the special case
-- statement:
--   Let each $S^i$ be a nonempty compact Hausdorff space with its Borel σ-algebra, let $S=\prod_jS^j$ carry the product topology and its Borel σ-algebra, and let each $h^i:S\to\mathbb R$ be continuous. Let $p$ be a probability measure on $S$ and $i$ a player. Assume that for every $t^i\in S^i$ and every Borel set $R^i\subseteq S^i$, the deviation $\zeta^i_{t,R}$ equal to $t^i$ on $R^i$ and to the identity elsewhere satisfies (4) for $p$: its integrand is integrable and
--   $$
--   \int_S\bigl[h^i(s)-h^i\bigl(s^{-i},\zeta^i_{t,R}(s^i)\bigr)\bigr]\,dp(s)\ \ge 0 .
--   $$
--   Then every Borel-measurable $\zeta^i:S^i\to S^i$ satisfies (4) for $p$: its integrand is integrable and
--   $$
--   \int_S\bigl[h^i(s)-h^i\bigl(s^{-i},\zeta^i(s^i)\bigr)\bigr]\,dp(s)\ \ge 0 .
--   $$
--
--   Together with the special case this shows that the cluster point $p$ satisfies (4) for every player and every measurable deviation, i.e. it is a correlated equilibrium.
--
--   **Formalization Note** The conclusion includes the integrability of the integrand, which is part of the formal definition of a correlated equilibrium in this mission.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 25, proof of Theorem 3, "The general case" ("For each k, fix some t_k^i ∈ A_k" through the end of the proof); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 25, the general case: if a probability measure `p` on `S` satisfies
(4) for player `i` and every special-case deviation (`tⁱ` on a Borel set `Rⁱ`, the identity
elsewhere), then it satisfies (4) for player `i` and every Borel-measurable `ζⁱ : Sⁱ → Sⁱ`. -/
theorem general_case_of_special_case {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (i : ι)
    (hspec : ∀ (t : S i) (R : Set (S i)), MeasurableSet R →
      Integrable
          (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
        0 ≤ ∫ s : Profile S,
          (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p)
    (ζ : S i → S i) (hζ : Measurable ζ) :
    Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p := by sorry

end HartSchmeidler.Compact
