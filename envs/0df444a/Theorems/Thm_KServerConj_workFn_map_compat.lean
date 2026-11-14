-- Prove2me | Theorems.Thm_KServerConj_workFn_map_compat
-- name    : KServerConj.workFn_map_compat
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T03:53:50.49019+00:00
-- url     : https://prove2.me/theorems/14576563-7feb-4091-859a-6d98a16873dd
-- title:
--   Work functions are preserved by injective isometries
-- statement:
--   Let $f:N\hookrightarrow M$ be an injective distance-preserving map between pseudometric spaces, let $k\ge1$, and let $C_0\subseteq N$ have cardinality $k$. Suppose the request histories agree under $f$ through time $T$. Then for every $t\le T$ and every $k$-point configuration $X\subseteq N$,
--
--   $$
--   w_t^M(f(C_0);f(X))=w_t^N(C_0;X).
--   $$
--
--   Thus passing to a larger pseudometric space creates no cheaper work-function value for a configuration and request history lying in the original space. In particular, the work function can be computed in a finite subspace containing the initial configuration, the request prefix, and the target configuration. Explicit injectivity is required because distance preservation alone need not imply injectivity in a pseudometric space.
-- source:
--   Finite-space reduction for Coester–Koutsoupias–Zbysiński, The k-server conjecture is true, arXiv:2609.15979, Theorem 1.3.

import Definitions.Def_KServerConj_confDist
import Definitions.Def_KServerConj_workFn

theorem KServerConj.workFn_map_compat {N M : Type*} [PseudoMetricSpace N] [PseudoMetricSpace M]
    (f : N ↪ M) (hd : ∀ x y, dist (f x) (f y) = dist x y)
    (k : ℕ) (hk : 1 ≤ k) (C₀ : Finset N) (hC₀ : C₀.card = k)
    (rN : ℕ → N) (rM : ℕ → M) (T : ℕ)
    (hreq : ∀ t, 1 ≤ t → t ≤ T → f (rN t) = rM t) :
    ∀ t, t ≤ T → ∀ X : Finset N, X.card = k →
      KServerConj.workFn k (C₀.map f) rM t (X.map f) = KServerConj.workFn k C₀ rN t X := by sorry
