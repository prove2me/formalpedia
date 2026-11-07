-- Prove2me | Theorems.Thm_MatchVec3_lemma_2_2
-- name    : MatchVec3.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:21.315132+00:00
-- url     : https://prove2.me/theorems/d14bdf5e-a2e0-47f6-9592-486c4f1dfaff
-- title:
--   Lemma 2.2: 2-restricted prime-power bound $T\le an+1$
-- statement:
--   Let $p$ be a prime and let $\gamma\ne0$ in $\mathbb Z_{p^a}$. If $(u_i,v_i)_{i=1}^T$ is a matching vector family over $\mathbb Z^n_{p^a}$ with all off-diagonal inner products equal to $\gamma$, then
--
--   $$T\le an+1.$$
--
--   This is the base of the induction on fibers: it bounds the short-sum fibers through Lemma 5.1.
--
--   Differences from the source: none.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.2, p.9

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily

namespace MatchVec3

/-- **Lemma 2.2 (2-restricted prime-power bound)** (Aggarwal, Obremski, STOC 2027 submission
(manuscript sha256 44199413…), Lemma 2.2, p.9): if `(u_i, v_i)_{i=1}^T` is a matching vector family
over `Z_{p^a}^n` with all off-diagonal inner products equal to `γ ≠ 0`, then `T ≤ an + 1`.

**Formalization Note** `γ ≠ 0` in `ZMod (p ^ a)` forces `a ≥ 1`. -/
theorem lemma_2_2 {p a n T : ℕ} (hp : p.Prime) (γ : ZMod (p ^ a)) (hγ : γ ≠ 0)
    (U V : Fin T → Fin n → ZMod (p ^ a)) (hfam : IsMVFamily U V)
    (hoff : ∀ i j, i ≠ j → U i ⬝ᵥ V j = γ) :
    T ≤ a * n + 1 := by sorry

end MatchVec3
