-- Prove2me | Theorems.Thm_ImplicitParityWL_footnote_3_color_removal
-- name    : ImplicitParityWL.footnote_3_color_removal
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:12:47.579303+00:00
-- url     : https://prove2.me/theorems/eb6ee6d9-be5c-4a81-9ab0-4a2d59b265e1
-- title:
--   Footnote 3 — removing vertex colors, preserving the first distinguishing round
-- statement:
--   There is an absolute constant $C$ such that the following holds for all $k\ge2$. Let $G,H$ be colored graphs on $N\ge1$ vertices each, first distinguished by $k$-WL after $T$ rounds. Then there are $n$ with $N\le n\le CN$ and uncolored simple graphs $G',H'$ on $n$ vertices, first distinguished by $k$-WL after $T'$ rounds, with
--   $$
--   T\le T'+k.
--   $$
--   A linear $n$ is what preserves the exponent $k-1$ of the mission's goal, since the number of colors can be of the order of $N$.
--
--   **Formalization Note** Uncolored $k$-WL is the published `OAI.VariableWL.histogram`.
--
--   Differences from the source:
--   - reading: footnote 3: using standard gadgets, one can remove the vertex colors while preserving all relevant properties (no formal statement; citation [61]) → the statement above, with n linear in N and T ≤ T′ + k; reason: the mission's own precise form of the relevant properties, the one the proof of Theorem 1.3 needs for uncolored graphs
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), footnote 3, p.10

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_ImplicitParityWL_WLColor

namespace ImplicitParityWL

/-- **Footnote 3** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.10), "one can remove the vertex colors while preserving all relevant properties", made precise for
the round count: there is an absolute constant `C` such that for all `k ≥ 2` and colored graphs `G`, `H` on `N ≥ 1` vertices
each, first distinguished by `k`-WL after `T` rounds, there are `N ≤ n ≤ C N` and uncolored graphs `G'`, `H'` on `n` vertices,
first distinguished by `k`-WL after `T'` rounds, with `T ≤ T' + k`.

**Formalization Note** The paper gives one sentence and a citation [61], and no formal statement; this statement is the
property of the gadget the proof of Theorem 1.3 needs for uncolored graphs. Uncolored `k`-WL is `OAI.VariableWL.histogram`. -/
theorem footnote_3_color_removal : ∃ C : ℕ, ∀ k : ℕ, 2 ≤ k →
    ∀ {K V W : Type} [Fintype V] [Fintype W] (G : ColoredGraph K V) (H : ColoredGraph K W) (N T : ℕ),
      1 ≤ N → Fintype.card V = N → Fintype.card W = N → FirstDistinguishedAt G H k T →
      ∃ n : ℕ, N ≤ n ∧ n ≤ C * N ∧ ∃ (G' H' : SimpleGraph (Fin n)) (T' : ℕ),
        OAI.VariableWL.histogram ⟨n, G'⟩ k T' ≠ OAI.VariableWL.histogram ⟨n, H'⟩ k T' ∧
        (∀ r < T', OAI.VariableWL.histogram ⟨n, G'⟩ k r = OAI.VariableWL.histogram ⟨n, H'⟩ k r) ∧
        T ≤ T' + k := by sorry

end ImplicitParityWL
