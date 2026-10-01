-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_transcendental
-- name    : LiouvilleDiffAlg.liouvilleForm_descent_transcendental
-- status  : Open
-- author  : @vebis
-- created : 2026-10-01T11:41:50.056433+00:00
-- url     : https://prove2.me/theorems/ab36d69f-694f-4e9b-a9cc-31bc9744a289
-- title:
--   Liouville descent for a transcendental generator
-- statement:
--   Let $G$ be a field of characteristic zero with a derivation $D$, let $F\subseteq G$ be a subfield and let $K$ be an intermediate field with $D(K)\subseteq K$ and $\operatorname{Con}(G)\subseteq K$. Let $t\in G$ be transcendental over $K$ and assume that $t$ is a logarithmic generator ($Dt=Ds/s$ for a nonzero $s\in K$) or an exponential generator ($Dt/t=Ds$ for some $s\in K$) over $K$. Put $L=K(t)$ and let $h\in K$. If $h$ has Liouville form in $L$, that is,
--
--   $$h=\sum_{j=1}^n c_j\frac{Du_j}{u_j}+Dv\qquad\text{with } c_j\in\operatorname{Con}(G),\ u_j\in L^{\times},\ v\in L,$$
--
--   then $h$ has Liouville form in $K$.
--
--   This combines the logarithmic and exponential cases of the descent step in the inductive proof of Liouville's theorem on elementary antiderivatives.
--
--   **Formalization Note** `LiouvilleFormIn` is the predicate defined in the module `LiouvilleDiffAlg_Form`.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem liouvilleForm_descent_transcendental {F G : Type*} [Field F] [Field G]
    [Differential G] [Algebra F G] [CharZero G] (K : IntermediateField F G)
    (hK : ∀ x ∈ K, x′ ∈ K) (hconst : constants G ⊆ (K : Set G)) {t : G}
    (htr : Transcendental K t)
    (hcase : (∃ s ∈ K, s ≠ 0 ∧ t′ = s′ / s) ∨ (∃ s ∈ K, t′ / t = s′))
    {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h := by sorry

end LiouvilleDiffAlg
