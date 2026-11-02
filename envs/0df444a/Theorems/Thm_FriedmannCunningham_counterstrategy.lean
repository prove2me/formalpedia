-- Prove2me | Theorems.Thm_FriedmannCunningham_counterstrategy
-- name    : FriedmannCunningham.counterstrategy
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-02T05:11:10.843852+00:00
-- url     : https://prove2.me/theorems/71f189e1-028c-4407-9f5b-e52ac65bc8cc
-- title:
--   Lemma 1 — optimal counterstrategy
-- statement:
--   For every n≥3 and every legal player-zero strategy in the explicit repeated-priority game, one legal player-one strategy minimizes the multiplicity valuation simultaneously at every starting vertex.
-- source:
--   Avis and Friedmann (2017), Lemma 1, §2.2. https://oliverfriedmann.com/downloads/papers/cunningham_exponential_lower_bound.pdf

import Definitions.Def_friedmann_cunningham

set_option autoImplicit false

namespace FriedmannCunningham

/-- Lemma 1 on the explicit repeated-priority family. A single legal opponent
strategy minimizes the multiplicity valuation from every starting vertex. -/
theorem counterstrategy (n : ℕ) (hn : 3 ≤ n)
    (σ : Fin (vertices n) → Fin (vertices n))
    (hσ : FriedmannParity.Legal (parityGame n) false σ) :
    ∃ τ : Fin (vertices n) → Fin (vertices n),
      FriedmannParity.Legal (parityGame n) true τ ∧
      ∀ v τ', FriedmannParity.Legal (parityGame n) true τ' →
        FriedmannMultiplicity.ValueLE (parityGame n)
          (FriedmannParity.playValue (parityGame n) σ τ v)
          (FriedmannParity.playValue (parityGame n) σ τ' v) := by sorry

end FriedmannCunningham
