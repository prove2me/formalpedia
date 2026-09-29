-- Prove2me | Theorems.Thm_KServer_lazyPot_le_of_pointwise
-- name    : KServer.lazyPot_le_of_pointwise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:21:23.599643+00:00
-- url     : https://prove2.me/theorems/f3ea717c-dc0a-4d0c-8fe6-350bf2d73769
-- title:
--   Reducing the update property to a bound on arbitrary witnesses
-- statement:
--   The technical heart of Bein–Chrobak–Larmore's three-server analysis is their Lemma 4, the assertion that
--   $$\Psi_{w,s} \;\le\; \hat\Psi_{w,r} \qquad\text{for every } s,$$
--   where $r$ is the last request. Its proof begins: *"Pick $p, a, a', b, b', d, d'$ such that*
--   $$\Psi_{w,s} = sr + sa + sa' - w(a,a') + pb + pb' - w(s,b,b') + dd' - w(s,p,d) - w(s,p,d')\text{,''}$$
--   and then splits into twelve cases according to which server travels to $r$ in each of the three work-function values.
--
--   That opening step is not innocent in a formal development. The lazy potential is
--   $$\Psi_{w,s} = \hat w(s) + \dot w(s), \qquad
--   \dot w(x) = \sup_{p,d,d'}\bigl(\tilde w(x,p) + dd' - w(x,p,d) - w(x,p,d')\bigr),$$
--   a sum of two suprema, the second of which *nests* a third — the copy of $\tilde w$ inside $\dot w$ — and on an unbounded metric space none of them need be attained. So "pick witnesses realising $\Psi_{w,s}$" is not literally available.
--
--   This lemma supplies that step. It says: to prove $\Psi_{w,s} \le \hat\Psi_{w,r}$ it suffices to prove the displayed expression is $\le \hat\Psi_{w,r}$ **for every choice** of the seven points, with no minimality assumed on any of them. The twelve-case analysis can then be carried out exactly as written in the paper, as a statement about arbitrary points, free of any $\varepsilon$.
--
--   ## The proof
--
--   Three applications of the same device. For a set $S$ bounded above and $\varepsilon > 0$ there is $t \in S$ with $\sup S \le t + \varepsilon$ — take $b = \sup S - \varepsilon$ in `exists_lt_of_lt_csSup`. Applying this with $\varepsilon/3$ to $\tilde w(r,s)$, to $\dot w(s)$, and to the inner $\tilde w(s,p)$ at the witness $p$ just produced, and using
--   $$\hat w(s) = d(s,r) + \tilde w(r,s)$$
--   — the fact that a maximizer of the shadow may be taken to contain the last request — assembles precisely the displayed expression, up to $\varepsilon$. Since $\varepsilon$ was arbitrary, `le_of_forall_pos_le_add` concludes.
--
--   The order of the three extractions matters: the third supremum is $\tilde w(s,p)$, whose argument $p$ is only produced by the second extraction, so the witnesses must be taken in the order $\tilde w(r,s)$, then $\dot w(s)$, then $\tilde w(s,p)$.
--
--   Boundedness of each supremum — needed both for the extraction and to know the potentials are not the junk value that `sSup` assigns to an unbounded set — comes from the unit-rate growth of the work function with base point at the relevant evaluation point.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3, Lemma 4 and its equation (4): 'Pick p, a, a', b, b', d, d' such that Psi_{w,s} = sr + sa + sa' - w(a,a') + pb + pb' - w(s,b,b') + dd' - w(s,p,d) - w(s,p,d')'.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lazyPot_le_of_pointwise (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r s : M)
    (h : ∀ a a' p b b' d d' : M,
      (dist s r + dist s a + dist s a' - workFnU C₀ (σ ++ [r]) ![r, a, a'])
        + ((dist p b + dist p b' - workFnU C₀ (σ ++ [r]) ![s, b, b'])
            + (dist d d' - workFnU C₀ (σ ++ [r]) ![s, p, d]
                - workFnU C₀ (σ ++ [r]) ![s, p, d']))
        ≤ semiLazyPot C₀ (σ ++ [r]) r) :
    lazyPot C₀ (σ ++ [r]) s ≤ semiLazyPot C₀ (σ ++ [r]) r := by sorry

end KServer
