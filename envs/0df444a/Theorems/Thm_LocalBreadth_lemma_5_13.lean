-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_13
-- name    : LocalBreadth.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:29.602421+00:00
-- url     : https://prove2.me/theorems/0df2f0c9-5f97-4c56-b60c-e797ebb1626b
-- title:
--   Lemma 5.13 — the protected forest exists, with finite protected sets and safe chains
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   The protected forest with formal copies exists. In every such forest, every vertex has finitely many ancestors and a finite set $P_v\subseteq L_v$, and for every $a\preceq v$ with $s_a>0$, the compressed chain $\overline H[a,v]$ is safe for $(L_a,N_a,s_a)$.
--
--   Differences from the source:
--   - encoding: "the construction" of the forest, with free choices → every term of the structure `ProtectedForest`; reason: each step of the recursion is a field, so a term is exactly one outcome of the construction
--   - reading: the numbered statement for the fixed-error forest of §§5.4–5.7 → the statement for the formal-copy forest of §5.8; reason: §5.8 states that these results apply with formal copies and compressed chains, and the goal needs that form
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.13, p.33; §5.8.3, pp.38–39

import Mathlib
import Definitions.Def_LocalBreadth_ProtectedForest

namespace LocalBreadth

/-- Lemma 5.13. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.33, with §5.8.3,
pp.38–39. The construction is well defined: a protected forest exists. Every vertex has finitely many
ancestors and a finite `P_v ⊆ L_v`, and for every `a ⪯ v` with `s_a > 0`, the chain `H[a, v]` is safe for
`(L_a, N_a, s_a)`.

**Formalization Note.** Finiteness of `P_v` is in the type `Finset ℤ`, so the content of "finite" is in the
existence clause. -/
theorem lemma_5_13 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) :
    Nonempty (ProtectedForest X) ∧
    ∀ F : ProtectedForest X, ∀ v,
      {a | IsAnc F.parent a v}.Finite ∧ (F.P v : Set ℤ) ⊆ F.L v ∧
      ∀ a, IsAnc F.parent a v → 0 < F.s a →
        IsSafe X (F.N a) (F.s a) (chainFrom F.L F.parent a v) := by sorry

end LocalBreadth
