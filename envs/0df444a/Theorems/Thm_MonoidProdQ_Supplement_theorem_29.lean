-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_29
-- name    : MonoidProdQ.Supplement.theorem_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:19:48.221951+00:00
-- url     : https://prove2.me/theorems/a7dacc0e-8fd5-4baf-bfd7-306b12686f66
-- title:
--   Theorem 29 — strong certificates and breadth: $\beta_{A_f}(M_f)=\beta(M_f)=b_f(U)$
-- statement:
--   Let $U$ and $O$ be finite sets and $f:2^U\to O$. Let $M_f=2^U/\!\sim_f$ be the extension monoid of $f$ (with $[S][T]=[S\cup T]$), $b_f(U)$ the strong-certificate number (Definition 4), and $A_f=\{[\emptyset]\}\cup\{[\{u\}]:u\in U\}$. Then
--
--   $$\beta_{A_f}(M_f)=\beta(M_f)=b_f(U),$$
--
--   where $\beta(M_f)$ is the product breadth over the full alphabet. Through Theorem 18 this turns small strong certificates into $O(\min\{n,\sqrt{n\,b_f(U)}\})$ query algorithms.
--
--   **Formalization Note** Subsets of $U$ are finite sets; $b_f(U)$ is a natural number, cast to $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source: none.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 29 (Strong certificates and breadth), p.41

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_Supplement_ExtMonoid
import Definitions.Def_MonoidProdQ_Supplement_strongCertNumber
import Definitions.Def_MonoidProdQ_Supplement_extAlphabet

universe u v

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 29 (Strong certificates and
breadth), p.41: "Let U and O be finite sets, and let f : 2^U → O be a function. Let M_f be the
extension monoid of f (Definition 3), and let b_f(U) be as in Definition 4. For the alphabet
A_f = {[∅]} ∪ {[{u}] : u ∈ U}, β_{A_f}(M_f) = β(M_f) = b_f(U)."

**Formalization Note.** Subsets of `U` are `Finset U`. `M_f` is `ExtMonoid f`, `A_f` is
`extAlphabet f`, `b_f(U)` is `strongCertNumber f`; `β(M_f)` is the breadth over the full
alphabet, `productBreadth univ`. Both equalities are in `ℕ∞` (`b_f(U)` cast). -/
theorem theorem_29 :
    ∀ (U : Type u) (O : Type v) [Fintype U] [DecidableEq U] [Fintype O] [DecidableEq O]
      (f : Finset U → O),
      productBreadth (extAlphabet f) = productBreadth (Finset.univ : Finset (ExtMonoid f)) ∧
        productBreadth (Finset.univ : Finset (ExtMonoid f)) = (strongCertNumber f : ℕ∞) := by sorry

end MonoidProdQ.Supplement
