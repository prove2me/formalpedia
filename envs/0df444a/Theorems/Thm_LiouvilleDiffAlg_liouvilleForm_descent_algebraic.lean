-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_algebraic
-- name    : LiouvilleDiffAlg.liouvilleForm_descent_algebraic
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T10:25:48.414395+00:00
-- url     : https://prove2.me/theorems/bf29e79b-a3a3-4db4-be9f-cb5237052df2
-- title:
--   Descent of Liouville form through an algebraic step
-- statement:
--   Let $G$ be a field of characteristic zero with a derivation $D$, let $F\subseteq G$ be a subfield, and let $K$ be an intermediate field with $D(K)\subseteq K$ and $\operatorname{Con}(G)\subseteq K$. Let $t\in G$ be algebraic over $K$ and put $L=K(t)$. Let $h\in K$. If $h$ has Liouville form in $L$, that is,
--
--   $$h=\sum_{j=1}^n c_j\frac{Du_j}{u_j}+Dv\qquad\text{with } c_j\in\operatorname{Con}(G),\ u_j\in L^{\times},\ v\in L,$$
--
--   then $h$ has Liouville form in $K$ (with the same kind of data $c_j\in\operatorname{Con}(G)$, $u_j\in K^{\times}$, $v\in K$).
--
--   This is the algebraic case of the descent step in the standard induction proving Liouville's theorem on elementary antiderivatives. Mathlib contains the corresponding statement for finite-dimensional extensions of differential fields as `isLiouville_of_finiteDimensional`.
--
--   **Formalization Note** Here $G$ is only assumed to carry a derivation and to have characteristic zero; the hypotheses `hK`, `hconst` and `hh` state $D(K)\subseteq K$, $\operatorname{Con}(G)\subseteq K$ and $h\in K$.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, section "Basic theorem"; proof: Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form

open scoped Differential

namespace LiouvilleDiffAlg

theorem liouvilleForm_descent_algebraic {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    (hconst : constants G ⊆ (K : Set G)) {t : G} (ht : IsAlgebraic K t) {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h := by sorry

end LiouvilleDiffAlg
