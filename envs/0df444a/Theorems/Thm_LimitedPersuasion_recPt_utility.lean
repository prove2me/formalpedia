-- Prove2me | Theorems.Thm_LimitedPersuasion_recPt_utility
-- name    : LimitedPersuasion.recPt_utility
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:49.483961+00:00
-- url     : https://prove2.me/theorems/69f9db70-4cf3-4dd9-a5b2-6b26c9ce9a37
-- title:
--   The recommendation points of a direct scheme form a point collection whose utilities are the scheme's, for both $S$ and $R$
-- statement:
--   Let $\varphi$ be a $k$-signal scheme, read as the direct scheme in which signal $j$ recommends action $j\in[k]$. For every set $C$ of types with $q_C>0$, the recommendation point
--   $$p(C)=\big(\mathbb E[u_R(\varphi)\mid C],\ \mathbb E[u_S(\varphi)\mid C]\big)$$
--   lies in the convex hull of the points $\{(\varrho(c),\xi(c)):c\in C\}$, so the recommendation points form a point collection $\mathcal P(\varphi)$, and
--   $$u_S(\mathcal P(\varphi))=\sum_{\sigma}v_\sigma(\sigma)=u_S(\varphi),\qquad u_R(\mathcal P(\varphi))=\sum_\sigma w_\sigma(\sigma)=u_R(\varphi),$$
--   the sender's and receiver's utilities when the receiver follows the recommendation.
--
--   This is the bridge between schemes and point collections used in Lemma 2 and Theorem 1.
--
--   Differences from the source:
--   - generalization: a direct and persuasive scheme in a symmetric instance (§3.1), $2\le k\le n$ → any $k$-signal scheme recommending action $j$ with signal $j$, in any instance, any $k\le n$; reason: the identities and the hull membership use neither persuasiveness, symmetry nor $k\ge2$, so the statement specializes to the paper's
--   - reading: $u_S(\varphi)$, $u_R(\varphi)$ of a direct scheme → the utilities when the receiver follows the recommendation; reason: §3's utilities of a direct scheme; with them the recommendation point is the conditional expected utility pair
--   - reading: recommendation point for every $C$ → the hull condition for $C$ with $q_C\ne0$; reason: the conditional expectation given $C$ is defined only when $q_C>0$
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, §3.1, p.6 ("Observe that the recommendation points of a direct and persuasive signaling scheme are a point collection, and the utility of the collection equals the utility of the scheme, for both S and R")

import Mathlib
import Definitions.Def_LimitedPersuasion_PointCollection

namespace LimitedPersuasion

/-- **Recommendation points form a point collection with the scheme's utilities**,
Gradwohl–Hahn–Hoefer–Smorodinsky, arXiv:2007.12489v2, §3.1, p.6 ("Observe that the
recommendation points of a direct and persuasive signaling scheme are a point collection, and the
utility of the collection equals the utility of the scheme, for both S and R").

For every `k`-signal scheme `φ`, read as the direct scheme in which signal `j` recommends action
`j ∈ [k]`: each recommendation point `p(C)` with `q_C ≠ 0` lies in the convex hull of the points
of `C`, `u_S(P(φ))` equals the sender's utility when the receiver follows the recommendation, and
`u_R(P(φ))` equals the receiver's.

**Formalization Note.** Persuasiveness, symmetry and distinct types are not assumed. -/
theorem recPt_utility {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ}
    (I : Instance T n) (hkn : k ≤ n) (φ : (Fin n → T) → Fin k → ℝ) (hφ : IsScheme φ) :
    I.IsPointCollection hkn (I.recPt hkn φ) ∧
      I.uSP hkn (I.recPt hkn φ) = I.followS φ (Fin.castLE hkn) ∧
      I.uRP hkn (I.recPt hkn φ) = I.followR φ (Fin.castLE hkn) := by sorry

end LimitedPersuasion
