-- Prove2me | Theorems.Thm_LosslessCond_Supplement_theorem_B_2
-- name    : LosslessCond.Supplement.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:26:46.304032+00:00
-- url     : https://prove2.me/theorems/04dff3e9-e685-49aa-a284-f35708d5b57b
-- title:
--   Theorem B.2 — multiparty local-to-global principle; $D_p(F)\le(p+1)s$
-- statement:
--   Let $p\ge2$ and $s\ge1$ be integers and let $F:X_1\times\cdots\times X_p\to Z$ be a total function, where $X_1,\dots,X_p$ and $Z$ are finite and every $X_i$ is nonempty. Suppose every product restriction $F|_{X'_1\times\cdots\times X'_p}$ to original subsets $X'_i\subseteq X_i$ with
--
--   $$
--   |X'_i|\le 2^{(p+2)s+1}\quad(1\le i\le p)
--   $$
--
--   has deterministic number-in-hand communication complexity at most $s$. Then
--
--   $$
--   D_p(F)\le (p+1)s .
--   $$
--
--   This is the multiparty form of the local-to-global principle: if all small product restrictions are easy, so is the whole function, for any finite output alphabet. The paper derives Theorem B.1 from it.
--
--   **Formalization Note** Product restrictions are families of `Finset`s `S i`; their complexity is `multiCost F S` and $D_p(F)$ is `Dp F`.
--
--   Differences from the source:
--   - encoding: product restrictions to original subsets $X'_i$ → families of `Finset`s `S i`, possibly with an empty factor, with cost `multiCost F S`; reason: an empty factor has cost $0\le s$, so the hypothesis says the same, and the cost of the restriction is the restricted function's own complexity
--   - encoding: players $1,\dots,p$ with input sets $X_1,\dots,X_p$ → players `i : Fin p` (indices $0,\dots,p-1$) with a dependent family `X : Fin p → Type`; reason: relabelling of the players, same instances
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem B.2, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_LosslessCond_Supplement_multiCost

namespace LosslessCond

namespace Supplement

/-- **Theorem B.2 (Multiparty local-to-global principle)** (Mackenzie, arXiv:2609.28691, held
version sha256 ce75e6d4…, p.26, PDF p.27). Let `p ≥ 2` and `s ≥ 1` be integers, and let
`F : X_1 × ⋯ × X_p → Z` be a total function on finite nonempty sets. If every product restriction
`F|_{X′_1×⋯×X′_p}` with `|X′_i| ≤ 2^{(p+2)s+1}` for `1 ≤ i ≤ p` has communication complexity at most
`s`, then `D_p(F) ≤ (p + 1)s`.

**Formalization Note** Players are indexed by `Fin p`, with input sets `X i` finite and nonempty
(Appendix B's standing assumption, p.25) and a finite output set `Z`. A product restriction is a
family `S i ⊆ X i` of original subsets, given as `Finset`s; its complexity is `multiCost F S`.
The hypothesis also ranges over restrictions with an empty factor, which have complexity `0 ≤ s`,
so it says the same as the paper's. -/
theorem theorem_B_2 {p : ℕ} (hp : 2 ≤ p) {X : Fin p → Type} [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)] {Z : Type} [Fintype Z] (F : (∀ i, X i) → Z) (s : ℕ) (hs : 1 ≤ s)
    (hloc : ∀ S : ∀ i, Finset (X i), (∀ i, (S i).card ≤ 2 ^ ((p + 2) * s + 1)) →
      multiCost F (fun i => (S i : Set (X i))) ≤ s) :
    Dp F ≤ (p + 1) * s := by sorry

end Supplement

end LosslessCond
