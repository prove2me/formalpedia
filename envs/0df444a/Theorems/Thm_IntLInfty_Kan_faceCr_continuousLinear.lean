-- Prove2me | Theorems.Thm_IntLInfty_Kan_faceCr_continuousLinear
-- name    : IntLInfty.Kan.faceCr_continuousLinear
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:10:38.765056+00:00
-- url     : https://prove2.me/theorems/61e1d680-3011-4923-870b-8bfeaf25573d
-- title:
--   The face maps of the Banach spaces of C^r forms on simplices are continuous linear
-- statement:
--   Let $r\ge 1$ and $n\ge 0$. For every $m$ and every $0\le i\le m+1$ the face map $d_i:\Omega^n_{C^r}(\Delta^{m+1})\to\Omega^n_{C^r}(\Delta^m)$ (restriction along the $i$-th affine coface) is a continuous linear map, and so is its restriction $d_i:\Omega^n_{closed}(\Delta^{m+1})\to\Omega^n_{closed}(\Delta^m)$ to closed forms. On the jet of a $C^r$ $n$-form $\omega$ (with $d\omega$ of class $C^r$) it is the jet of the pullback, $$d_i\,j^r(\omega)=j^r\big((d^i)^*\omega\big),$$ and the face maps satisfy the simplicial identities $$d_a\,d_{b+1}=d_b\,d_a\qquad(a\le b).$$
--
--   Role: the face maps of the simplicial Banach space $\Omega^n_{C^r}(\Delta^\bullet)$ as continuous linear operators, used by the horn-filler and Kan-fibration steps of Theorem 5.10.
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, Convention 5.1 and proof of Lemma 5.9, pp. 14-15 (the simplicial Banach spaces of forms)

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

set_option autoImplicit false

namespace IntLInfty.Kan

theorem faceCr_continuousLinear (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (∀ (m : ℕ) (i : Fin (m + 2)),
      ∃ F : CrForms r (m + 1) n →L[ℝ] CrForms r m n, ∀ w, F w = faceCr r m n i w) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)),
      ∃ F : CrClosed r (m + 1) n →L[ℝ] CrClosed r m n, ∀ w, F w = faceCl r m n i w) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)) (w : CrForms r (m + 1) n) (ω : Ω (m + 1)),
      IsDeg n ω → IsCr r ω → jet r ω = w →
        (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)) (w : CrClosed r (m + 1) n) (ω : Ω (m + 1)),
      IsDeg n ω → IsCr r ω → IsClosedForm ω → jet r ω = w →
        (faceCl r m n i w : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ (m : ℕ) (a b : Fin (m + 2)), a ≤ b → ∀ w : CrForms r (m + 2) n,
      faceCr r m n a (faceCr r (m + 1) n b.succ w) =
        faceCr r m n b (faceCr r (m + 1) n a.castSucc w)) := by sorry

end IntLInfty.Kan
