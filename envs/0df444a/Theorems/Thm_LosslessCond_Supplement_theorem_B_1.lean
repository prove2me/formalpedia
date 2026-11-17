-- Prove2me | Theorems.Thm_LosslessCond_Supplement_theorem_B_1
-- name    : LosslessCond.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:26:10.878819+00:00
-- url     : https://prove2.me/theorems/67613f5c-2ba2-4ab5-b36e-5fc994d28484
-- title:
--   Theorem B.1 — multiparty condensation; restrictions of size $\le 2^{(p+2)s+1}$ with $D_p\ge\lceil c/(p+1)\rceil$
-- statement:
--   Let $p\ge2$ and let $F:X_1\times\cdots\times X_p\to Z$ be a total function, where $X_1,\dots,X_p$ and $Z$ are finite and every $X_i$ is nonempty. Write $c=D_p(F)$ for its deterministic number-in-hand communication complexity and suppose $c\ge p+2$. Put $s=\lfloor (c-1)/(p+1)\rfloor$. Then there are nonempty original subsets $X'_i\subseteq X_i$ such that
--
--   $$
--   |X'_i|\le 2^{(p+2)s+1}\quad(1\le i\le p),\qquad D_p\bigl(F|_{X'_1\times\cdots\times X'_p}\bigr)\ge\left\lceil \frac{c}{p+1}\right\rceil .
--   $$
--
--   For fixed $p$, the restricted inputs need only $O_p(c)$ bits to index while their communication complexity remains $\Omega_p(c)$, for any finite output alphabet.
--
--   **Formalization Note** Players are indexed by `Fin p`; $D_p$ is `Dp` and the complexity of the restriction is `multiCost F S`. $s$ is the natural-number quotient `(c - 1) / (p + 1)` (the floor) and $\lceil c/(p+1)\rceil$ is `Nat.ceil` of a rational.
--
--   Differences from the source:
--   - encoding: original subsets $X'_i\subseteq X_i$ and $D_p(F|_{X'_1\times\cdots\times X'_p})$ → `Finset`s `S i` and `multiCost F S` (least depth of a protocol correct on the product); reason: Lean convention, the same cost as the restricted function's own complexity
--   - encoding: players $1,\dots,p$ with input sets $X_1,\dots,X_p$ → players `i : Fin p` (indices $0,\dots,p-1$) with a dependent family `X : Fin p → Type`; reason: relabelling of the players, same instances
--   - encoding: $s=\lfloor (c-1)/(p+1)\rfloor$ and $\lceil c/(p+1)\rceil$ → `(c - 1) / (p + 1)` (ℕ division) and `⌈(c : ℚ) / (p + 1)⌉₊`; reason: ℕ division is the floor and `c - 1` is exact since $c\ge p+2$; `Nat.ceil` of the rational is the ceiling of a nonnegative number
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem B.1, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_LosslessCond_Supplement_multiCost

namespace LosslessCond

namespace Supplement

/-- **Theorem B.1 (Multiparty condensation)** (Mackenzie, arXiv:2609.28691, held version sha256
ce75e6d4…, p.26, PDF p.27). Let `p ≥ 2` and let `F : X_1 × ⋯ × X_p → Z` be a total function on
finite nonempty sets. Write `c = D_p(F)` and suppose `c ≥ p + 2`. Put `s = ⌊(c − 1)/(p + 1)⌋`. There
are nonempty original subsets `X′_i ⊆ X_i` such that `|X′_i| ≤ 2^{(p+2)s+1}` for `1 ≤ i ≤ p` and
`D_p(F|_{X′_1×⋯×X′_p}) ≥ ⌈c/(p + 1)⌉`.

**Formalization Note** Players are indexed by `Fin p`, with input sets `X i` finite and nonempty
and a finite output set `Z`; `D_p` is `Dp` and the restricted complexity is `multiCost F S` for
`S i = X′_i` (number-in-hand, public blackboard, outputs in `Z`). `s` is the natural-number
quotient `(c - 1) / (p + 1)`, which is the floor (and `c - 1` is exact since `c ≥ p + 2`);
`⌈c/(p + 1)⌉` is `Nat.ceil` of the rational `c / (p + 1)`. -/
theorem theorem_B_1 {p : ℕ} (hp : 2 ≤ p) {X : Fin p → Type} [∀ i, Fintype (X i)]
    [∀ i, Nonempty (X i)] {Z : Type} [Fintype Z] (F : (∀ i, X i) → Z) (c : ℕ) (hc : Dp F = c)
    (hcp : p + 2 ≤ c) :
    ∃ S : ∀ i, Finset (X i), (∀ i, (S i).Nonempty) ∧
      (∀ i, (S i).card ≤ 2 ^ ((p + 2) * ((c - 1) / (p + 1)) + 1)) ∧
      ⌈(c : ℚ) / (p + 1)⌉₊ ≤ multiCost F (fun i => (S i : Set (X i))) := by sorry

end Supplement

end LosslessCond
