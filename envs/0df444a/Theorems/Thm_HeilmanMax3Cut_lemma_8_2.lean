-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_8_2
-- name    : HeilmanMax3Cut.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:52.706197+00:00
-- url     : https://prove2.me/theorems/5006e58b-2df1-4b5c-9907-ad8405180725
-- title:
--   Lemma 8.2 — simplex trigonometric estimate
-- statement:
--   For every $m=(m_1,m_2,m_3)\in\Delta_3$, with $b=1/3$,
--
--   $$3+2\sum_{i=1}^3\cos(2\pi m_i)\ \ge\ 6\sum_{i=1}^3(m_i-b)^2 .$$
--
--   The estimate is the trigonometric input to the first-mode gain (Lemma 8.3).
--
--   Differences from the source:
--   - encoding: m ∈ Δ₃ ⊆ ℝ³ → m : Fin 3 → ℝ in Delta3; reason: coordinates 0, 1, 2 for 1, 2, 3
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 8.2, Eq. (87), p.27

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Delta3
open Real

namespace HeilmanMax3Cut

/-- **Lemma 8.2 (simplex trigonometric estimate).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 8.2, Eq. (87), p.27: "For any
`m = (m₁, m₂, m₃) ∈ Δ₃`, `3 + 2 ∑_{i=1}^3 cos(2πmᵢ) ≥ 6 ∑_{i=1}^3 (mᵢ − b)²`", with `b = 1/3`. -/
theorem lemma_8_2 :
    ∀ m ∈ Delta3, 6 * ∑ i, (m i - 1 / 3) ^ 2 ≤ 3 + 2 * ∑ i, Real.cos (2 * π * m i) := by sorry

end HeilmanMax3Cut
