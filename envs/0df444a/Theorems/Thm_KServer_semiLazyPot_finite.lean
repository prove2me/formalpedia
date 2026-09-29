-- Prove2me | Theorems.Thm_KServer_semiLazyPot_finite
-- name    : KServer.semiLazyPot_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:12:19.534691+00:00
-- url     : https://prove2.me/theorems/86cdb70e-dbe4-44bc-b661-f3341c03c973
-- title:
--   The semi-lazy potential is finite
-- statement:
--   The semi-lazy potential $\hat\Psi = \max\{\Psi, \Lambda, \Gamma\}$ of Bein–Chrobak–Larmore is built from suprema ranging over *all* points of the metric space, which is not assumed bounded, finite or compact. This says all three are bounded above, with the uniform bound
--   $$\hat\Psi_{w,x} \;\le\; 4K_x, \qquad K_x := \sum_i d\bigl(x, C_0(i)\bigr).$$
--
--   ## Why the statement is needed and not routine
--
--   In this formalization `sSup` of a set unbounded above is $0$. The entire potential argument consists of inequalities between these suprema — the offset property, the update property, and the metric-specific comparisons $\Lambda \le \Psi$, $\Gamma \le \Psi$ — and every one of them would be a statement about junk values rather than about the intended quantities if any supremum were unbounded. So this is a prerequisite for the whole development, not a technicality.
--
--   It is also not automatic. Each of $\Lambda$ and $\Gamma$ contains **positive** terms that grow without bound as their witnesses recede from $x$; finiteness depends on exact cancellation against the subtracted work-function values.
--
--   ## The mechanism
--
--   Everything follows from the unit-rate growth of the work function, always applied with base point $x$: for three-point configurations pinned at $x$,
--   $$w(x,e,e') \;\ge\; d(x,e) + d(x,e') - K_x .$$
--   This yields, in turn,
--   $$\hat w(x) \le K_x, \qquad \tilde w(x,y) \le 2\,d(y,x) + K_x, \qquad \dot w(x) \le 3K_x,$$
--   and hence $\Psi = \hat w + \dot w \le 4K_x$.
--
--   For $\Lambda_{w,x} = \sup_{p,q,e,e'}\bigl(-xp + \tilde w(x,p) - xq + \tilde w(x,q) - w(x,p,q) + ee' - w(x,e,e')\bigr)$, the bound on $\tilde w$ gives $-xp + \tilde w(x,p) \le d(x,p) + K_x$, which *grows* with $p$; the same for $q$. The saving grace is $-w(x,p,q) \le -d(x,p) - d(x,q) + K_x$, which cancels both, and $ee' - w(x,e,e') \le K_x$ by the triangle inequality through $x$. The four residual copies of $K_x$ are the bound.
--
--   For $\Gamma_{w,x} = \sup_{p,q,d,d',f}\bigl(-xp + \tilde w(x,p) + xq + dd' - w(x,q,d) - w(x,q,d') + qf - w(x,p,f)\bigr)$ the cancellation is tighter still: the $q$-terms contribute $+d(x,q)$ from $xq$, $-2d(x,q)$ from the two work-function values and $+d(x,q)$ from $qf$, summing to exactly zero; the $p$-, $d$-, $d'$- and $f$-terms each cancel in pairs. Again four copies of $K_x$ remain.
--
--   So both auxiliary potentials obey the same bound as $\Psi$, and the maximum of the three does too.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3 (definitions of Psi, Lambda, Gamma and Psi-hat = max of the three); the finiteness of these suprema is used implicitly throughout Sections 3 and 4.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem semiLazyPot_finite (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (x : M) :
    semiLazyPot C₀ σ x ≤ 4 * ∑ i, dist x (C₀ i) := by sorry

end KServer
