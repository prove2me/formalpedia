-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_exponential
-- name    : LiouvilleDiffAlg.liouvilleForm_descent_exponential
-- status  : Open
-- author  : @vebis
-- created : 2026-10-01T10:25:58.406171+00:00
-- url     : https://prove2.me/theorems/7fe7f50a-c569-4abe-be56-58b1ae32441f
-- title:
--   Descent of Liouville form through an exponential step
-- statement:
--   Let $G$ be a field of characteristic zero with a derivation $D$, let $F\subseteq G$ be a subfield, and let $K$ be an intermediate field with $D(K)\subseteq K$ and $\operatorname{Con}(G)\subseteq K$. Let $t\in G$ be an exponential generator over $K$: $t$ is transcendental over $K$ and $Dt/t=Ds$ for some $s\in K$. Put $L=K(t)$ and let $h\in K$. If $h$ has Liouville form in $L$, that is,
--
--   $$h=\sum_{j=1}^n c_j\frac{Du_j}{u_j}+Dv\qquad\text{with } c_j\in\operatorname{Con}(G),\ u_j\in L^{\times},\ v\in L,$$
--
--   then $h$ has Liouville form in $K$.
--
--   This is the exponential case of the descent step in the standard induction proving Liouville's theorem on elementary antiderivatives.
--
--   **Formalization Note** Here $G$ is only assumed to carry a derivation and to have characteristic zero; the hypotheses `hK`, `hconst` and `hh` state $D(K)\subseteq K$, $\operatorname{Con}(G)\subseteq K$ and $h\in K$.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, section "Basic theorem"; proof: Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form

open scoped Differential

namespace LiouvilleDiffAlg

theorem liouvilleForm_descent_exponential {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    (hconst : constants G ⊆ (K : Set G)) {t : G} (ht : IsExponentialOver K t) {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h := by sorry

end LiouvilleDiffAlg
