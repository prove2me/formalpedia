-- Prove2me | Theorems.Thm_KServer_workFnU_lipschitz
-- name    : KServer.workFnU_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:29:41.723499+00:00
-- url     : https://prove2.me/theorems/efdee527-14c1-410d-b08a-8dddfa8b4df0
-- title:
--   The Lipschitz property of the unified work function
-- statement:
--   For any work function $w$ and any two configurations $X$ and $Y$,
--
--   $$|w(X) - w(Y)| \;\le\; XY,$$
--
--   where $XY$ is the cost of a minimum-cost matching between the two configurations. Equivalently, in the form stated, $w(X) \le w(Y) + YX$.
--
--   ## Role
--
--   This is the *Lipschitz property*, one of the three basic tools — alongside the triangle inequality and quasiconvexity — with which every calculation in the work-function literature is carried out. It says nothing more than that an offline schedule reaching $Y$ can be extended to one reaching $X$ by moving the servers directly, but it is used constantly to replace a configuration by a nearby one at a controlled cost.
--
--   Its characteristic use is in geometric reductions: to push a free point $b$ occurring in a potential out to a distinguished point $u$, one writes $pb = pu - bu$ and then discards $bu$ against the Lipschitz bound $w(u,b') \le w(b,b') + bu$, obtaining $pb - w(b,b') \le pu - w(u,b')$.
--
--   **Formalization note.** The statement is for the unified work function, which minimises over relabellings of the target configuration. It follows from the labelled version by evaluating both sides at a relabelling optimal for $Y$: the matching cost is invariant under simultaneously relabelling both configurations.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 2: 'Note that |w(X) - w(Y)| <= XY for any work function w and any configurations X and Y. This inequality we call the Lipschitz property.'

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ σ Y + moveCost Y X := by sorry

end KServer
