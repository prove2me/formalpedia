-- Prove2me | Theorems.Thm_JechSetTheory_fodor
-- name    : JechSetTheory.fodor
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T02:28:19.667768+00:00
-- url     : https://prove2.me/theorems/0dcb610e-f3b3-4db1-86e2-2f82172574e4
-- title:
--   Jech, Theorem 8.7 (Fodor) — a regressive function on a stationary set is constant on a stationary set
-- statement:
--   Let $\kappa$ be a regular uncountable cardinal. A set $S \subseteq \kappa$ is **stationary** if it meets every closed unbounded subset of $\kappa$, and an ordinal function $f$ on $S$ is **regressive** if $f(\alpha) < \alpha$ for every nonzero $\alpha \in S$ (Jech, Definition 8.6).
--
--   **Theorem (Fodor; Jech 8.7).** If $f$ is a regressive function on a stationary set $S \subseteq \kappa$, then there are a stationary set $T \subseteq S$ and an ordinal $\gamma < \kappa$ such that
--
--   $$f(\alpha) = \gamma \quad\text{for all } \alpha \in T .$$
--
--   Fodor's "pressing-down" lemma is the basic tool of stationary-set combinatorics: it converts a regressive assignment into a single value taken stationarily often, and it is exactly the principle behind the splitting theorems of the chapter and behind the counting arguments used in Silver's theorem.
--
--   **Formalization Note** Ordinals below $\kappa$ form the type `Below k`, so $\gamma < \kappa$ is expressed by the existential witness being an element of that type; "nonzero" is rendered as "not a minimal element" of the well-order.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 93, Theorem 8.7 (Fodor), with Definition 8.6 (regressive function), p. 93

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem fodor (k : Cardinal) (hk : k.IsRegular) (hk₀ : ℵ₀ < k)
    (S : Set (Below k)) (hS : IsStationary S) (f : Below k → Below k)
    (hf : IsRegressiveOn S f) :
    ∃ T ⊆ S, IsStationary T ∧ ∃ c : Below k, ∀ x ∈ T, f x = c := by sorry

end JechSetTheory
