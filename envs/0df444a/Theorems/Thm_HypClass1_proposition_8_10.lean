-- Prove2me | Theorems.Thm_HypClass1_proposition_8_10
-- name    : HypClass1.proposition_8_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:39:27.80811+00:00
-- url     : https://prove2.me/theorems/382f287f-22c0-4348-afd0-77054ecaa22f
-- title:
--   Proposition 8.10 — a $p$-spread measure on $\mathcal B$ gives $q_f(\mathcal B)\le p$
-- statement:
--   Let $p \in [0,1]$, let $\mathcal B \subseteq 2^X$ be a non-empty increasing family, and let $\nu$ be a $p$-spread probability measure on $\mathcal B$. Then
--   $$
--   q_f(\mathcal B) \le p .
--   $$
--
--   Differences from the source: none.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 8.10, p.43

import Mathlib
import Definitions.Def_HypClass1_IsIncreasing
import Definitions.Def_HypClass1_qf
import Definitions.Def_HypClass1_IsSpread

namespace HypClass1

/-- **Proposition 8.10 (a spread measure bounds the fractional expectation-threshold).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…),
Proposition 8.10, p.43: "Let p ∈ [0, 1]. Let B ⊆ 2^X be a non-empty increasing family and
ν : B → [0, 1] be a p-spread measure. Then q_f(B) ≤ p."

**Formalization Note.** `X` is the finite type `α`; `ν` is a probability distribution on `2^X`
supported on `B` (`IsSpread`). -/
theorem proposition_8_10 {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (B : Finset (Finset α)) (hB : B.Nonempty) (hinc : IsIncreasing B)
    (ν : PMF (Finset α)) (hν : IsSpread p B ν) :
    qf B ≤ p := by sorry

end HypClass1
