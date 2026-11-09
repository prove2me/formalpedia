-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_boolean_border_identity
-- name    : OddPermSum.Evaluation.boolean_border_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:21:44.690198+00:00
-- url     : https://prove2.me/theorems/9c370464-144e-4f94-8964-c97a8dd3f50f
-- title:
--   Lemma 3.5 — fixed Boolean border identity and invertibility
-- statement:
--   Let $A\in F^{n\times n}$ over a characteristic-two field have rank $r=n-k$. Select an invertible $r\times r$ minor with row and column sets $I,J$, and use their increasing complement lists to fix the standard-basis border $U,V$. For $M_X(t)$ as in (3.9), both conclusions hold:
--
--   $$M_A(t)\text{ is invertible for every }t\in F^k,$$
--   $$\Phi_n(X)=\sum_{\varepsilon\in\{0,1\}^k}\Phi\big(M_X(\varepsilon)\big).$$
--
--   The second equality is an identity in the formal polynomial ring in the independent entries of $X$. The chosen border is fixed throughout, so it can be differentiated even over $F_2$. Original row and column orders are retained; $k=0$ gives a single summand.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: the selected minor A[I,J] and every bordered matrix M_A(t) are invertible over F → unit determinant for the selected minor in RankBorder and for each bordered matrix in the conclusion; reason: these are precisely the source's invertible matrices; the original A may be singular, and a unit determinant over F is equivalent to invertibility
--   - encoding: identity for every X with U,V fixed, explicitly polynomial in the proof → equality in MvPolynomial (Fin n × Fin n) F using the generic matrix X; reason: preserves formal differentiation over finite fields and includes every numerical specialization
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 8, Lemma 3.5, Eqs. (3.9)–(3.10), proof p. 9

import Definitions.Def_OddPermSum_Evaluation_phi
import Definitions.Def_OddPermSum_Evaluation_border

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 3.5, including invertibility for every t and the identity as a formal
polynomial in X. The complement maps remain fixed under differentiation. -/
theorem boolean_border_identity {F : Type*} [Field F] [CharP F 2]
    (n k : ℕ) (A : Matrix (Fin n) (Fin n) F) (b : RankBorder A k) :
    (∀ t : Fin k → F, IsUnit (border b.rows b.cols A t).det) ∧
    (oddPolynomial F n =
      ∑ ε : Fin k → Bool,
        phi (border b.rows b.cols
          (fun i j => (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) F))
          (fun a => MvPolynomial.C (if ε a then (1 : F) else 0)))) := by sorry

end OddPermSum.Evaluation
