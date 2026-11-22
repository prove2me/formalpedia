-- Prove2me | Theorems.Thm_JetLocalCompactness
-- name    : JetLocalCompactness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:19.275749+00:00
-- url     : https://prove2.me/theorems/f7821876-3b3e-4315-8664-6778d0f83e70
-- title:
--   Jet Local Compactness: Jet Local Compactness
-- statement:
--   Arzela-Ascoli on an open set, in the sequential form the blow-up argument needs:
--   a sequence of `ℝ × Plane`-valued maps that is, from some index on, continuous,
--   uniformly bounded and uniformly equicontinuous on each compact subset of an open
--   `W` has ONE subsequence converging uniformly on every compact subset of `W`.
--
--   The pair-valued codomain is the point:  the paper's compact family (eq:compact) is a
--   closure in `C^1`, and per the run's interface decision the `C^1` topology on a
--   compact base is the `C^0` topology on the jet `z ↦ (v z, Dv z)`.  Carrying the jet
--   means one application of this lemma yields uniform convergence of the functions AND
--   of their gradients along the same subsequence, which is what limit passage in the
--   weak equation consumes.
--
--   The hypotheses are required only for `n ≥ N` with `N` depending on the compact set,
--   because the blow-ups are defined on domains that grow as the scale shrinks, so no
--   bound is available at small indices.  Nothing here is about `p`-harmonicity.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetLocalCompactness.lean#L18-L159
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetLocalCompactness.lean#L18-L159

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetLocalCompactness
set_option autoImplicit false

theorem JetLocalCompactness (W : Set Plane) (hW : IsOpen W) (J : ℕ → Plane → ℝ × Plane)
    (hunif : ∀ K : Set Plane, K ⊆ W → IsCompact K →
      ∃ (N : ℕ) (A : ℝ),
        (∀ n, N ≤ n → ContinuousOn (J n) K) ∧
        (∀ n, N ≤ n → ∀ z ∈ K, ‖J n z‖ ≤ A) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n, N ≤ n → ∀ z ∈ K, ∀ z' ∈ K,
          dist z z' < δ → dist (J n z) (J n z') ≤ ε)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Jlim : Plane → ℝ × Plane,
      ∀ K : Set Plane, K ⊆ W → IsCompact K →
        TendstoUniformlyOn (fun i => J (φ i)) Jlim Filter.atTop K := by sorry
