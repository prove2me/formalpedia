-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_S6_5
-- name    : IntADSat.Supplement.theorem_S6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:59:59.236108+00:00
-- url     : https://prove2.me/theorems/ea918be4-6fc0-4661-bdb2-ddaa961ddfbd
-- title:
--   Theorem S6.5 — complete classification of the principal moment fibre at index two (Godsil–McKay switch)
-- statement:
--   Let $G$ be a graph on $n$ vertices with $I_G=2$, let $v$ be its unique nonzero binary obstruction, and put $S=\operatorname{supp}(v)$. The principal moment fibre of $G$ has at most two graph isomorphism classes. It has exactly two if and only if all of the following hold:
--
--   1. $|S|=4$;
--   2. the induced graph $G[S]$ is regular;
--   3. every vertex outside $S$ has zero, two, or four neighbours in $S$;
--   4. the four vertices in $S$ have the same total degree in $G$.
--
--   In that case the unique other member is the Godsil–McKay switch on $S$: replace the two neighbours in $S$ of each outside vertex having two neighbours by the other two vertices. If any condition fails, $G$ is determined by its principal moments.
--
--   Example S6.8 shows that the bound of two classes is attained.
--
--   **Formalization Note** "At most two classes" is stated as: of any two members of the fibre, one is isomorphic to $G$ or they are isomorphic to each other ($G$ lies in its own fibre). "Exactly two" is: some member of the fibre is not isomorphic to $G$.
--
--   Differences from the source:
--   - encoding: I_G = 2; v its unique nonzero binary obstruction → Nat.card (ℤⁿ/Λ_G) = 2; v any binary obstruction; reason: v is unique by Theorem S6.4, so quantifying over all of them is the same statement
--   - reading: the fibre has at most two isomorphism classes; it has exactly two → any two fibre members H₁, H₂ satisfy G ≅ H₁ ∨ G ≅ H₂ ∨ H₁ ≅ H₂; some fibre member is not isomorphic to G; reason: G belongs to its own fibre, so these are the class counts
--   - reading: the unique other member is the Godsil–McKay switch on S → the switch is in the fibre, is not isomorphic to G, and every fibre member not isomorphic to G is isomorphic to it; reason: the meaning of "the unique other member" up to isomorphism
--   - encoding: G[S] regular; total degree in G; Godsil–McKay switch → all vertices of S have the same number of neighbours in S; IntADSat.deg; gmSwitch G S (defined for any S, flipping the cross edges of outside vertices with two neighbours in S); reason: for |S| = 4 the switch replaces the two neighbours in S by the other two, as on the page
--   - encoding: the principal moment fibre of G; determined by its principal moments → H : SimpleGraph (Fin m) for every m; reason: every finite simple graph is isomorphic to one on Fin m, and moments and isomorphism are invariant under relabelling; the empty-word moment forces m = n
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S6.5, p.44 (PDF 45)

import Mathlib
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_Supplement_MomentEquiv
import Definitions.Def_IntADSat_Supplement_IsBinaryObstruction
import Definitions.Def_IntADSat_Supplement_Determined
import Definitions.Def_IntADSat_Supplement_gmSwitch

set_option autoImplicit false

namespace IntADSat.Supplement

open Classical in
/-- **Theorem S6.5 (Complete classification at index two)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.44 (PDF 45)). Suppose `I_G = 2`, let `v`
be its unique nonzero binary obstruction, and put `S = supp(v)`. The principal moment fibre has at most two
graph isomorphism classes. It has exactly two if and only if all of the following hold: (1) `|S| = 4`;
(2) the induced graph `G[S]` is regular; (3) every vertex outside `S` has zero, two, or four neighbours in
`S`; (4) the four vertices in `S` have the same total degree in `G`. In that case the unique other member is
the Godsil–McKay switch on `S`. If any condition fails, `G` is determined by its principal moments.

**Formalization Note** `I_G = |ℤⁿ/Λ_G| = 2` (`Nat.card`); `v` is any binary obstruction (it is unique by
Theorem S6.4). "At most two classes": among any two fibre members, one is isomorphic to `G` or they are
isomorphic to each other (`G` is in its own fibre). "Exactly two": some fibre member is not isomorphic to `G`.
`G[S]` regular: all vertices of `S` have the same number of neighbours in `S`. Total degree is
`IntADSat.deg`. The switch is `gmSwitch G S`. -/
theorem theorem_S6_5 {n : ℕ} (G : SimpleGraph (Fin n))
    (hI : Nat.card ((Fin n → ℤ) ⧸ IntADSat.wordLattice G) = 2)
    (v : Fin n → ZMod 2) (hv : IsBinaryObstruction G v) :
    let S := Finset.univ.filter fun i => v i ≠ 0
    let conds : Prop :=
      S.card = 4 ∧
      (∃ d : ℕ, ∀ i ∈ S, (S.filter fun j => G.Adj i j).card = d) ∧
      (∀ x ∉ S, (S.filter fun j => G.Adj x j).card ∈ ({0, 2, 4} : Finset ℕ)) ∧
      (∀ i ∈ S, ∀ j ∈ S, IntADSat.deg G i = IntADSat.deg G j)
    (∀ (m₁ m₂ : ℕ) (H₁ : SimpleGraph (Fin m₁)) (H₂ : SimpleGraph (Fin m₂)),
      MomentEquiv G H₁ → MomentEquiv G H₂ →
      Nonempty (G ≃g H₁) ∨ Nonempty (G ≃g H₂) ∨ Nonempty (H₁ ≃g H₂)) ∧
    ((∃ (m : ℕ) (H : SimpleGraph (Fin m)), MomentEquiv G H ∧ IsEmpty (G ≃g H)) ↔ conds) ∧
    (conds →
      MomentEquiv G (gmSwitch G S) ∧ IsEmpty (G ≃g gmSwitch G S) ∧
      ∀ (m : ℕ) (H : SimpleGraph (Fin m)), MomentEquiv G H → IsEmpty (G ≃g H) →
        Nonempty (H ≃g gmSwitch G S)) ∧
    (¬ conds → Determined G) := by sorry

end IntADSat.Supplement
