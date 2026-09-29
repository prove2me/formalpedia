-- Prove2me | Theorems.Thm_JechSetTheory_isClub_diagInter
-- name    : JechSetTheory.isClub_diagInter
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T02:27:14.976717+00:00
-- url     : https://prove2.me/theorems/d1857e23-cc7c-4aa5-82ff-344428db0e1c
-- title:
--   Jech, Lemma 8.4 — the diagonal intersection of clubs is club
-- statement:
--   Let $\kappa$ be a regular uncountable cardinal. Recall that $C \subseteq \kappa$ is **closed unbounded** (*club*) if it is unbounded in $\kappa$ and contains all its limit points below $\kappa$, and that the **diagonal intersection** of a family $\langle X_\alpha : \alpha < \kappa \rangle$ of subsets of $\kappa$ is
--
--   $$\mathop{\triangle}_{\alpha<\kappa} X_\alpha \;=\; \Bigl\{ \xi < \kappa \;:\; \xi \in \bigcap_{\alpha<\xi} X_\alpha \Bigr\}.$$
--
--   **Lemma (Jech 8.4).** If $C_\alpha$ is closed unbounded in $\kappa$ for every $\alpha < \kappa$, then $\mathop{\triangle}_{\alpha<\kappa} C_\alpha$ is closed unbounded in $\kappa$.
--
--   Equivalently (Jech, Corollary 8.5) the closed unbounded filter on $\kappa$ is *normal*. Normality is what makes the club filter rigid enough to support the pressing-down argument of Fodor's theorem, and with it the whole theory of stationary sets; the dual statement is that the nonstationary ideal is closed under diagonal unions.
--
--   **Formalization Note** Clubs live on the type `Below k` of ordinals below $\kappa$, so the family is indexed by that same type and the side condition $\xi < \kappa$ of equation (8.3) is carried by the type rather than by a hypothesis. The regularity and uncountability of $\kappa$ are hypotheses of the statement, as in Jech's standing assumption for Definition 8.1.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 92, Lemma 8.4 (with the diagonal intersection of equation (8.3), p. 92)

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem isClub_diagInter (k : Cardinal) (hk : k.IsRegular) (hk₀ : ℵ₀ < k)
    (X : Below k → Set (Below k)) (hX : ∀ a, IsClub (X a)) :
    IsClub (diagInter X) := by sorry

end JechSetTheory
