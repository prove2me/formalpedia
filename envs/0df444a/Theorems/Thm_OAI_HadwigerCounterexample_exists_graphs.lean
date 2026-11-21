-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_exists_graphs
-- name    : OAI.HadwigerCounterexample.exists_graphs
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T21:55:41.002327+00:00
-- url     : https://prove2.me/theorems/209c9beb-4058-495b-b8d1-38596ca4f93f
-- title:
--   Theorem 1.1 — arbitrarily large $\alpha\le2$ graphs with small connected matchings
-- statement:
--   This is the main result of the source preprint (Theorem 1.1, p. 3). There are arbitrarily large integers $m$ for which an $m$-vertex finite simple graph $G$ satisfies
--   $$\alpha(G)\le2\quad\text{and}\quad \mathrm{cm}(G)<\frac{m}{100},$$
--   where $\alpha(G)$ is the independence number and $\mathrm{cm}(G)$ is the connected-matching number (the largest size of a matching whose edges are pairwise touching). Precisely, for every bound $M$ there is an $m\ge\max(M,5)$ and a graph $G$ on $m$ vertices with these properties.
--
--   Combined with the matching–minor bound (Proposition 3.5), this forces the Hadwiger number below $m/2$ while the chromatic number is at least $m/2$, disproving Hadwiger's conjecture. The graphs are produced by a probabilistic frame construction over $\mathbb F_2$; the constant $1/100$ is the paper's fixed linear coefficient.
--
--   **Formalization Note.** Transcribed from the authors' Lean theorem `OAI.HadwigerCounterexample.exists_graphs` (`Main.lean`). Graphs are `SimpleGraph (Fin m)`; $\alpha$ is `indepNum` (an `ℕ∞`); $\mathrm{cm}$ is the natural-valued `connectedMatchingNumber`, cast to `ℚ` for the strict inequality. The lower bound $m\ge5$ ensures nonemptiness and matches the authors' statement.
-- source:
--   https://github.com/openai/math/blob/main/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf , p. 3, Theorem 1.1; authors' Lean: https://github.com/openai/math/blob/main/lean/OAI/Combinatorics/HadwigerCounterexample/Main.lean

import Mathlib
import Definitions.Def_HadwigerMatching_Defs
import Definitions.Def_ListHadwiger

open OAI.HadwigerMatching OAI.LinearListHadwiger

namespace OAI.HadwigerCounterexample

theorem exists_graphs (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G : ℚ) < (m : ℚ) / 100 := by sorry

end OAI.HadwigerCounterexample
