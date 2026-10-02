-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_liouville_basic_theorem
-- name    : LiouvilleDiffAlg.liouville_basic_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T19:11:47.2168+00:00
-- url     : https://prove2.me/theorems/3a3ee2a9-a26c-453f-bd9a-f2e0375c4dd7
-- title:
--   Liouville's theorem (differential algebra)
-- statement:
--   Let $F \subseteq G$ be differential fields of characteristic zero with the same constants, $\operatorname{Con}(F) = \operatorname{Con}(G)$, and suppose that $G$ is an elementary differential extension of $F$. Suppose $f \in F$ and $g \in G$ satisfy $Dg = f$ (that is, $G$ contains an antiderivative of $f$). Then there exist $n \ge 0$, constants $c_1, \dots, c_n \in \operatorname{Con}(F)$, nonzero elements $f_1, \dots, f_n \in F$ and $s \in F$ such that
--   $$f = c_1\frac{Df_1}{f_1} + \cdots + c_n\frac{Df_n}{f_n} + Ds.$$
--
--   In words: if $f$ has an antiderivative in an elementary extension of $F$, then that antiderivative is an element of $F$ plus a constant linear combination of logarithms of elements of $F$. This is the theorem on which the Risch algorithm is based.
--
--   **Formalization Note** The characteristic-zero hypothesis is not written in the source article. It is the standing convention of the theorem in its standard references (Rosenlicht 1972; Geddes–Czapor–Labahn §12.4). The equality of constants is stated as: the image of $\operatorname{Con}(F)$ in $G$ equals $\operatorname{Con}(G)$.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Basic theorem"

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic

open scoped Differential

namespace LiouvilleDiffAlg

theorem liouville_basic_theorem {F G : Type*} [Field F] [Field G] [Differential F]
    [Differential G] [Algebra F G] [DifferentialAlgebra F G] [CharZero F]
    (hcon : algebraMap F G '' constants F = constants G)
    (helem : IsElementaryDifferentialExtension F G)
    (f : F) (g : G) (hg : g′ = algebraMap F G f) :
    ∃ (n : ℕ) (c : Fin n → F) (u : Fin n → F) (v : F),
      (∀ i, c i ∈ constants F) ∧ (∀ i, u i ≠ 0) ∧
      f = ∑ i, c i * ((u i)′ / u i) + v′ := by sorry

end LiouvilleDiffAlg
