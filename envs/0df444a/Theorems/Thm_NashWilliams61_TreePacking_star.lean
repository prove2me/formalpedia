-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_star
-- name    : NashWilliams61.TreePacking.star
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:50.119981+00:00
-- url     : https://prove2.me/theorems/d015688a-0610-4d10-b506-28b5e9c3bf53
-- title:
--   (*) — critical [crucial] sets with non-empty intersection are closed under $\cap$ and $\cup$
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$, $k \ge 1$, $g : V \to \mathbb Z_{\ge 0}$ and $s \ge 0$. A non-empty $X \subseteq V$ is *critical* if $\Delta_G(X) = 0$ and *crucial* if $\Gamma(X) = 0$, where $\Gamma(X) = \Delta_G(X) - s + g\,.\,\bar X$. Let $X, Y \subseteq V$ with $X \cap Y \ne \emptyset$.
--
--   1. If $[G, g]$ is a couple and $X, Y$ are critical, then $X \cap Y$ and $X \cup Y$ are critical.
--   2. If $[G, g]$ is $s$-good and $X, Y$ are crucial, then $X \cap Y$ and $X \cup Y$ are crucial.
--
--   In symbols, under the respective hypotheses,
--   $$\Delta_G(X) = \Delta_G(Y) = 0 \implies \Delta_G(X \cap Y) = \Delta_G(X \cup Y) = 0,$$
--   and likewise for $\Gamma$. These closure properties produce the vertices $\xi, \eta$ between which the new edge of Lemma 3 is placed.
--
--   **Formalization Note** The page invokes only "$\Delta_G$ and $\Gamma$ are non-negative on non-empty subsets"; accordingly the critical part assumes that $[G,g]$ is a couple and the crucial part that it is $s$-good. Non-emptiness of $X$ and $Y$ follows from $X \cap Y \neq \emptyset$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 446, proof of Lemma 3, claim (*) and Eq. (2)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Couples
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **(\*)** (Nash-Williams 1961, p. 446). In a couple `[G, g]`, if `X, Y` are critical
(`Δ_G = 0`, non-empty) and `X ∩ Y ≠ ∅`, then `X ∩ Y` and `X ∪ Y` are critical; in an
`s`-good couple, the same holds for crucial sets (`Γ = 0`, non-empty). -/
theorem star {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (g : V → ℕ) (s : ℕ) (X Y : Finset V) (hXY : (X ∩ Y).Nonempty) :
    (IsCouple k ends g → Delta k ends X = 0 → Delta k ends Y = 0 →
        Delta k ends (X ∩ Y) = 0 ∧ Delta k ends (X ∪ Y) = 0) ∧
      (IsGood k ends g s → Gamma k ends g s X = 0 → Gamma k ends g s Y = 0 →
        Gamma k ends g s (X ∩ Y) = 0 ∧ Gamma k ends g s (X ∪ Y) = 0) := by sorry

end NashWilliams61.TreePacking
