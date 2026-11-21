-- Prove2me | Theorems.Thm_OAI_HadwigerMatching_full_matching_minor_proposition
-- name    : OAI.HadwigerMatching.full_matching_minor_proposition
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T21:55:11.225334+00:00
-- url     : https://prove2.me/theorems/cbf9bd3d-f8e7-4ddb-84e8-6c89a65393c0
-- title:
--   Proposition 3.5 — the matching–minor bound
-- statement:
--   Proposition 3.5 of the source preprint (p. 15). For every finite nonempty graph $G$ of order $m$, with Hadwiger number $h(G)$ and connected-matching number $\mathrm{cm}(G)$,
--   $$h(G)\le\frac{m+4\,\mathrm{cm}(G)+2}{3}.$$
--   In particular, if $\alpha(G)\le2$, $\mathrm{cm}(G)<m/100$ and $m\ge5$, then
--   $$h(G)<\frac{26m}{75}+\frac23<\frac m2\le\chi(G).$$
--
--   The bound counts small branch sets in a complete-minor model: the singleton branches form a clique and can be paired, and together with the two-vertex branches they form one touching matching, which controls the deficit. This is the counting inequality that converts the connected-matching bound of Theorem 1.1 into a clique-minor estimate, following the connected-matching approach of Cambie.
--
--   **Formalization Note.** Transcribed verbatim from the authors' Lean theorem `OAI.HadwigerMatching.full_matching_minor_proposition` (`HadwigerMatching/Main.lean`). The order $m$, Hadwiger number $h$ and connected-matching number $c$ are introduced as `let`-bindings; inequalities are over `ℚ`; $\chi$ is represented by `chromaticNumber.toNat` (finite on a finite graph).
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 15, Proposition 3.5; authors' Lean: https://github.com/openai/math/blob/main/lean/OAI/Combinatorics/HadwigerMatching/Main.lean

import Mathlib
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger

open OAI.HadwigerMatching OAI.LinearListHadwiger

namespace OAI.HadwigerMatching

theorem full_matching_minor_proposition
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    let m : ℕ := Fintype.card V
    let h : ℕ := LinearListHadwiger.hadwigerNumber G
    let c : ℕ := HadwigerMatching.connectedMatchingNumber G
    (h : ℚ) ≤ ((m : ℚ) + 4 * (c : ℚ) + 2) / 3 ∧
      (G.indepNum ≤ 2 →
        (c : ℚ) < (m : ℚ) / 100 →
        5 ≤ m →
        (h : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
        26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧
        (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ)) := by sorry

end OAI.HadwigerMatching
