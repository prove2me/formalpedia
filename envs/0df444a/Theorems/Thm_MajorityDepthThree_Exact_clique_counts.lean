-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_clique_counts
-- name    : MajorityDepthThree.Exact.clique_counts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:50.226587+00:00
-- url     : https://prove2.me/theorems/93f9e1fd-17ce-47f7-a07d-6b2dabf74bb7
-- title:
--   Fact 3.2 — clique counts and full extremality
-- statement:
--   Let $\ell\ge k\ge1$, let $V$ be the $\ell$-element carrier, and let $K_\ell^{(k)}$ contain every positive $k$-clause on $V$. This is a monotone $k$-uniform $(\ell-k+1)$-extremal CNF. With $t=\ell-k+1$,
--
--   $$|V|=\ell,\quad |K_\ell^{(k)}|=\binom\ell k,\quad \tau(K_\ell^{(k)})=t,\quad
--   \Theta(\ell,t,k)=\theta_t(K_\ell^{(k)})=\binom\ell t.$$
--
--   Extremality is measured against all signed threshold formulas, not a separately stipulated monotone maximum. This gives the source's complete clique fact, including the six weight-two solutions of the four-variable three-clique used in the equality construction.
--
--   Differences from the source:
--   - encoding: n Boolean variables → The fixed carrier Fin n with ambient set univ; reason: Relabeling preserves clauses, assignments, weights and top fan-in; the theorem retains its stated parameter domain
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.8, Fact 3.2 and Definition 3.1

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem clique_counts (ell k : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ell) :
    let V : Finset (Fin ell) := Finset.univ
    let F := clique V k
    V.card = ell ∧ ValidCNF V F ∧ Uniform k F ∧ Monotone F ∧
    F.card = Nat.choose ell k ∧ tau V F = some (ell - k + 1) ∧
    Extremal V F (ell - k + 1) k ∧
    thetaMax V (ell - k + 1) k = theta V F (ell - k + 1) ∧
    theta V F (ell - k + 1) = Nat.choose ell (ell - k + 1) := by sorry

end MajorityDepthThree.Exact
