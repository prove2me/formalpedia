-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_orderIso_extends_of_le_succ
-- name    : Grunbaum2003.skeleton_orderIso_extends_of_le_succ
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:29.961782+00:00
-- url     : https://prove2.me/theorems/a41db648-7492-4ce5-9bc2-2e0ed522fdaa
-- title:
--   Extension of $k$-skeleton order isomorphisms when $d \le k + 1$
-- statement:
--   This theorem establishes that when the ambient dimension $d$ satisfies $d \le k + 1$, every order isomorphism between the $k$-skeletons of two $d$-polytopes extends to an order isomorphism of their complete face lattices.
--
--   Let $d, k \in \mathbb{N}$ satisfy $d \le k + 1$, let $P, Q \subseteq \mathbb{R}^d$ be $d$-polytopes (`IsDPolytope P`, `IsDPolytope Q`), and let $\varphi : \operatorname{skel}_k(P) \xrightarrow{\sim} \operatorname{skel}_k(Q)$ be an order isomorphism of their $k$-skeletons. Then there exists an order isomorphism
--
--   $$
--   \Phi : \mathcal{F}(P) \xrightarrow{\;\sim\;} \mathcal{F}(Q) \quad \text{such that} \quad \forall F \in \operatorname{skel}_k(P),\; \Phi(F) = \varphi(F).
--   $$
--
--   When $d \le k + 1$, every proper face of a $d$-polytope has affine dimension at most $d - 1 \le k$ and therefore already belongs to the $k$-skeleton $\operatorname{skel}_k(P)$, leaving only the improper top face ($P$ or $Q$) outside $\operatorname{skel}_k$. This immediately discharges the low-dimension cases ($d \le 2$ for graph reconstruction $k = 1$, and $d \le k + 1$ for general skeleton reconstruction).
--
--   **Formalization Note** The extension $\Phi$ is constructed via `skeleton_orderIso_extends_of_downSet_image` by mapping every face in `SkeletonFace P k` via $\varphi$ and mapping the improper face $P$ to $Q$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.1, p. 226

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace

set_option autoImplicit false

namespace Grunbaum2003

theorem skeleton_orderIso_extends_of_le_succ (d k : ℕ) (hdk : d ≤ k + 1)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P k ≃o SkeletonFace Q k) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P k, Φ F.val = (φ F).val := by sorry

end Grunbaum2003
