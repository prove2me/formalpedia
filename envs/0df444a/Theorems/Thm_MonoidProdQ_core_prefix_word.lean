-- Prove2me | Theorems.Thm_MonoidProdQ_core_prefix_word
-- name    : MonoidProdQ.core_prefix_word
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:51:20.123228+00:00
-- url     : https://prove2.me/theorems/b826da37-ffcd-4acf-b194-f2bb1616a994
-- title:
--   Proof of Theorem 18: a word of length $r$ with no proper product-preserving subword
-- statement:
--   Let $M$ be a finite commutative aperiodic monoid, $G\subseteq M$ with $1\in G$ and $\beta_G(M)\ge1$, let $n\ge1$ and put
--
--   $$r=\min\Big\{\beta_G(M),\Big\lfloor\frac{n+1}2\Big\rfloor\Big\}.$$
--
--   Then there is a word $w=a_1\cdots a_r\in G^r$ of length exactly $r$ that has no proper product-preserving scattered subword (every scattered subword $u\preceq w$ with $[u]=[w]$ is $w$ itself), and none of its letters $a_i$ is the identity.
--
--   This word supplies the hard inputs of the lower bound in Theorem 18.
--
--   Differences from the source:
--   - encoding: $r=\min\{\beta_G(M),\lfloor (n+1)/2\rfloor\}$ → `(min (productBreadth G) (((n + 1) / 2 : ℕ) : ℕ∞)).toNat`; reason: the minimum is taken in `ℕ∞` first, so it is finite and equals $\lfloor (n+1)/2\rfloor$ when $\beta_G(M)=\infty$
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), proof of Theorem 18, p.34

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_productBreadth

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), proof of Theorem 18, p.34: "For the lower
bound, suppose 1 ∈ G and β_G(M) ≥ 1, and put r = min{β_G(M), ⌊(n+1)/2⌋}. Choose a word
w = a₁ ⋯ a_r ∈ G^r with no proper product-preserving subword. Such a word is obtained by taking a
prefix of length r of a shortest product core of length at least r. In particular, none of the aᵢ
is the identity." A word over `G` of length exactly `r` whose only product-preserving scattered
subword is itself, with no letter equal to `1`.

**Formalization Note.** `r` is computed in `ℕ∞` and converted to a natural number (it is finite
since `⌊(n+1)/2⌋` is). -/
theorem core_prefix_word {M : Type*} [CommMonoid M] [Finite M] (hM : IsAperiodic M)
    (G : Finset M) (hG : (1 : M) ∈ G) (hβ : 1 ≤ productBreadth G) (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : List M, (∀ a ∈ w, a ∈ G) ∧
      w.length = (min (productBreadth G) (((n + 1) / 2 : ℕ) : ℕ∞)).toNat ∧
      (∀ u : List M, u.Sublist w → u.prod = w.prod → u = w) ∧ ∀ a ∈ w, a ≠ 1 := by sorry

end MonoidProdQ
