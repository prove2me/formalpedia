-- Prove2me | Theorems.Thm_MulticastPoS_lemma_E_1
-- name    : MulticastPoS.lemma_E_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:38:53.926529+00:00
-- url     : https://prove2.me/theorems/8854c2aa-0f57-4274-9248-b7c315744326
-- title:
--   Lemma E.1 — $H_{32}<5$ and $H_{8L^2}\le 5H_L$ for $L\ge 4$
-- statement:
--   The harmonic numbers satisfy $H_{32}<5$, and
--
--   $$
--   H_{8L^2}\le 5H_L\quad\text{for every integer } L\ge 4.
--   $$
--
--   These are the two numerical bounds that make every load range of the decomposition cost at most $10\,OPT$.
--
--   Differences from the source: none.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma E.1, Appendix E, p.16 (PDF p.17)

import Mathlib

namespace MulticastPoS

/-- Lemma E.1, the constants in the load-range bound (Huang–Yuan, *An O(log log n) Upper Bound on
the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), Appendix E, p.16): `H₃₂ < 5`, and `H_{8L²} ≤ 5 H_L` for every integer
`L ≥ 4`.

**Formalization Note** `H_m` is Mathlib's `harmonic m : ℚ`, cast to `ℝ`. -/
theorem lemma_E_1 :
    (harmonic 32 : ℝ) < 5 ∧
      ∀ L : ℕ, 4 ≤ L → (harmonic (8 * L ^ 2) : ℝ) ≤ 5 * harmonic L := by sorry

end MulticastPoS
