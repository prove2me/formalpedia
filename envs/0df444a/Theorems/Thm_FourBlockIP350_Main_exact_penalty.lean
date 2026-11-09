-- Prove2me | Theorems.Thm_FourBlockIP350_Main_exact_penalty
-- name    : FourBlockIP350.Main.exact_penalty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:21.924183+00:00
-- url     : https://prove2.me/theorems/70444106-39a9-41b4-a0ab-9306497e3bfc
-- title:
--   Lemma 3.1 — Exact penalty
-- statement:
--   Assume every variable has finite integral bounds and every interval is nonempty, and define $F$ by (3.1)–(3.2), with $K=W+1$. At every integer global vector $x$, the inner minimum is attained by a local vector and its uniquely determined integral residual; in particular $F(x)$ is finite.
--
--   Let $x^\star$ minimize $F$ in the global box and let $y^\star$ attain its inner minimum. Then
--   $$I\text{ is feasible}\ \Longleftrightarrow\ b-Zx^\star-Ey^\star=0,\quad \ell^{(1:n)}\le y^\star\le u^{(1:n)}.$$
--   Whenever feasible, $(x^\star,y^\star)$ is an optimal solution of the original program. This makes the penalized minimizer an exact feasibility and optimality test.
--
--   Differences from the source:
--   - encoding: attaining pair (y,s) with Ey+s=b−Zx → attaining y and s defined as b−Zx−Ey; extended-real value equals the finite integer candidate; reason: the equality uniquely determines s, so existence of y establishes both attainment and finiteness without assuming either
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 7, Lemma 3.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_Penalty

namespace FourBlockIP350.Main

open scoped BigOperators

theorem exact_penalty {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (I : FourBlock k n) (hbox : GoodBox I) :
    (∀ x : ZVec k, ∃ y : LocalCol k n → ℤ, Attains I x y) ∧
    ∀ xstar : ZVec k, GlobalBox I xstar →
      (∀ x, GlobalBox I x → F I xstar ≤ F I x) →
      ∀ ystar, Attains I xstar ystar →
        ((∃ z, Feasible I.program z) ↔
          residual I xstar ystar = 0 ∧ LocalBox I ystar) ∧
        ((∃ z, Feasible I.program z) → Optimal I.program (joinPoint xstar ystar)) := by sorry

end FourBlockIP350.Main
