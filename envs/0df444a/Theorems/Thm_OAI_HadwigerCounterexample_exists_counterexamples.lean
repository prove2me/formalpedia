-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_exists_counterexamples
-- name    : OAI.HadwigerCounterexample.exists_counterexamples
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T21:56:53.876191+00:00
-- url     : https://prove2.me/theorems/4be2f69e-db29-47f0-be03-c5aebf751d2f
-- title:
--   Main consequence — full rational bounds and $h<\chi$
-- statement:
--   The bundled headline consequence of the source preprint, combining Theorem 1.1 and Corollary 1.2. For every bound $M$ there is an $m\ge\max(M,5)$ and a graph $G$ on $m$ vertices with $\alpha(G)\le2$, $\mathrm{cm}(G)<m/100$, and the full chain of rational bounds
--   $$h(G)<\frac{26m}{75}+\frac23<\frac m2\le\chi(G),$$
--   together with the strict separation $h(G)<\chi(G)$ and the fact that $\chi(G)$ is finite (equal to its natural value `chromaticNumber.toNat`, not $\top$).
--
--   This is the authors' own combined formal statement; it records the ordinary-chromatic consequences explicitly, including finiteness of the chromatic number, and directly yields the failure of Hadwiger's inequality.
--
--   **Formalization Note.** Transcribed verbatim from the authors' Lean theorem `OAI.HadwigerCounterexample.exists_counterexamples` (`Main.lean`). Inequalities are over `ℚ`; `G.chromaticNumber ≠ ⊤` and `G.chromaticNumber = ↑(G.chromaticNumber.toNat)` assert finiteness of the chromatic number.
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 3, Theorem 1.1 and Corollary 1.2; authors' Lean: https://github.com/openai/math/blob/main/lean/OAI/Combinatorics/HadwigerCounterexample/Main.lean

import Mathlib
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger

open OAI.HadwigerMatching OAI.LinearListHadwiger

namespace OAI.HadwigerCounterexample

theorem exists_counterexamples (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G : ℚ) < (m : ℚ) / 100 ∧
      (hadwigerNumber G : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
      26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧ (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ) ∧
      hadwigerNumber G < G.chromaticNumber.toNat ∧
      G.chromaticNumber ≠ ⊤ ∧ G.chromaticNumber = ↑(G.chromaticNumber.toNat) := by sorry

end OAI.HadwigerCounterexample
