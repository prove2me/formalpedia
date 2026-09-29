-- Prove2me | Theorems.Thm_LiuVanRyzin_cutoff_strictMono_convex
-- name    : LiuVanRyzin.cutoff_strictMono_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:36:57.289989+00:00
-- url     : https://prove2.me/theorems/ca5514ca-df63-4ff4-a601-4d48be84a899
-- title:
--   Proposition 2 — the threshold $v(q)$ is strictly increasing in $q$, and convex when $u'''\ge 0$
-- statement:
--   Let $u$ be a customer utility as in Proposition 1, let $p_2<p_1$, and let $v(q)$ be the purchase threshold at fill rate $q$. Then
--
--   1. $v(q)$ is strictly increasing on $q\in[0,1)$;
--   2. if moreover $u$ is three times continuously differentiable on $(0,\infty)$ with $u'''(x)\ge 0$ for all $x>0$ (prudence), then $v(q)$ is convex on $[0,1)$.
--
--   $$0\le q<q'<1 \implies v(q)<v(q').$$
--
--   A lower fill rate, i.e. a larger rationing risk, induces more customers to buy early at the high price; this is the lever the firm pulls in the stocking decision.
--
--   **Formalization Note** The paper's "has the nonnegative third derivative" is read as: $u$ is $C^3$ on $(0,\infty)$ and its third derivative is nonnegative there. Both parts are stated on $q\in[0,1)$, the range of Proposition 1.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1120, Proposition 2

import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

/-- Proposition 2 (Liu–van Ryzin 2008, p. 1120). The threshold `v(q)` is strictly increasing in
`q ∈ [0, 1)`; it is moreover convex in `q` if the utility has a nonnegative third derivative. -/
theorem cutoff_strictMono_convex (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) :
    StrictMonoOn (fun q => cutoff u p₁ p₂ q) (Set.Ico 0 1) ∧
      (ContDiffOn ℝ 3 u (Set.Ioi 0) → (∀ x : ℝ, 0 < x → 0 ≤ iteratedDeriv 3 u x) →
        ConvexOn ℝ (Set.Ico 0 1) (fun q => cutoff u p₁ p₂ q)) := by sorry

end LiuVanRyzin
