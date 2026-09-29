-- Prove2me | Theorems.Thm_KServer_ck_potential_offset
-- name    : KServer.ck_potential_offset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T21:12:43.518123+00:00
-- url     : https://prove2.me/theorems/08675880-0fb4-4ffe-8e02-471fa294a5c7
-- title:
--   The offset property of the Coester-Koutsoupias potential
-- statement:
--   The Coester–Koutsoupias potential for $k$ servers is
--   $$\Phi_{x_1 \dots x_k}(w) \;=\; \sum_{i=0}^{k} w\bigl(\bar x_i^{\,i}\, x_{i+1} \dots x_k\bigr),$$
--   a sum of $k+1$ work-function values in which the $i$-th term places $i$ servers at the antipode of $x_i$. For $k = 3$ it reads
--   $$\Phi_{x y z}(w) \;=\; w(x,y,z) + w(\bar x, y, z) + w(\bar y, \bar y, z) + w(\bar z, \bar z, \bar z).$$
--   Whatever the points and whatever the map $x \mapsto \bar x$, this is bounded above by
--   $$4 \min_X w(X) + 12\Delta,$$
--   where $\Delta$ bounds the diameter of the space.
--
--   ## Role
--
--   This is the **offset property** of the potential — one of the two hypotheses under which a potential certifies competitiveness of the Work Function Algorithm, the other being the update property. Coester and Koutsoupias dispose of it in a sentence: the potential is a sum of $k+1$ work-function values, each of which differs from $\min_X w(X)$ by at most $k$ times the diameter, so the whole is at most $(k+1)\min_X w(X)$ plus a constant depending only on the space. The constant is what the additive term in the definition of competitiveness absorbs.
--
--   Two features are worth noting. First, the bound holds for **every** choice of $x, y, z$, hence in particular for the minimising choice that defines the potential — so no argument about where the minimum is attained is needed here. Second, the antipode map plays no role: the estimate uses only that each summand is a work-function value, so it is insensitive to which points are chosen and to whether they are genuinely antipodal. The antipodes matter for the update property, not for this one.
--
--   **Formalization note.** Each of the four summands is compared to $w(X)$ by the Lipschitz property of the work function, $w(Y) \le w(X) + d(X,Y)$, and the matching cost between two three-point configurations is at most $3\Delta$ termwise. Summing the four estimates is a single linear step.
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, arXiv:2102.10474, Section 3, proof of the potential theorem: 'the last inequality is due to the fact that Phi(w_T) is a sum of distances (which are absorbed by the constant c_M) and k+1 work function values, each of which differs from min_X w_T(X) by at most k times the diameter of M due to 1-Lipschitzness of w_T'. Stated here for k = 3, with the potential written out via the antipode map.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem ck_potential_offset (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (Δ : ℝ) (hΔ : ∀ u v : M, dist u v ≤ Δ) (bar : M → M) (x y z : M) (X : Config 3 M) :
    workFnU C₀ σ ![x, y, z] + workFnU C₀ σ ![bar x, y, z]
      + workFnU C₀ σ ![bar y, bar y, z] + workFnU C₀ σ ![bar z, bar z, bar z]
      ≤ 4 * workFnU C₀ σ X + 12 * Δ := by sorry

end KServer
