-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_equiv
-- name    : GenCMu.HeavyTraffic.proposition_2_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:46.110465+00:00
-- url     : https://prove2.me/theorems/3816b996-4538-4838-9523-b854605ee3ec
-- title:
--   Proposition 2, (35) — $\tilde W^n$ converges $\Leftrightarrow$ $\tilde T^n$ converges $\Leftrightarrow$ $\tilde N^n$ converges, and then $\tilde\tau^n$ converges
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumption 1 and let $T^n$ be feasible work-conserving policies. Then the following are equivalent, each convergence being uniform on $[0,1]$ to some limit function:
--   1. $\tilde W^n$ converges;
--   2. $\tilde T^n$ converges;
--   3. $\tilde N^n$ converges.
--
--   If they hold, $\tilde\tau^n$ converges uniformly on $[0,1]$ to some limit function.
--
--   Convergence of a policy sequence can therefore be read off any one of the class workloads, the allocation fluctuations or the headcounts.
--
--   **Formalization Note** The paper states (35) as "$\tilde W^n$ converges ⇔ $\tilde T^n$ converges ⇔ $\tilde N^n$ converges ⇔ $\tilde\tau^n$ converges". We state the first three equivalences and the implication to $\tilde\tau^n$. The converse implication from $\tilde\tau^n$ fails in the uniform topology: a policy that stops serving one class for $c\sqrt n$ time units right after the job arriving just before a fixed time $nt_0$ makes $\tilde\tau^n$ converge to a limit with a jump at $t_0$, while the continuous $\tilde T^n$ drops by an amount of order $c$ over a window of length $O(n^{-1/2})$ and has no uniform limit. The explicit post-horizon allocation condition supplies the post-horizon control needed at $t=1$.
--
--   The added `PostHorizonRegular` hypothesis requires $T^n_k(n+s\sqrt n)-T^n_k(n)=\rho_k(1)s\sqrt n+o(\sqrt n)$ uniformly for bounded $s\ge0$. It supplies the service behavior that the paper leaves unspecified after $n$.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), p. 818, Proposition 2, (35)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 2, (35) (p. 818): `W̃ⁿ` converges iff `T̃ⁿ` converges iff `Ñⁿ` converges,
and then `τ̃ⁿ` converges, uniformly on `[0,1]`. The converse from delay convergence is
not valid in the uniform topology without further regularity. -/
theorem proposition_2_equiv {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n)) (hpost : PostHorizonRegular H M T) :
    ((∃ Ws : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Wt T) Ws atTop (Set.Icc 0 1)) ↔
        (∃ Ts : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Ttil T) Ts atTop (Set.Icc 0 1))) ∧
    ((∃ Ts : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Ttil T) Ts atTop (Set.Icc 0 1)) ↔
        (∃ Ns : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Nt T) Ns atTop (Set.Icc 0 1))) ∧
    ((∃ Ws : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.Wt T) Ws atTop (Set.Icc 0 1)) →
        ∃ τs : ℝ → Fin d → ℝ, TendstoUniformlyOn (H.taut T) τs atTop (Set.Icc 0 1)) := by sorry
end GenCMu.HeavyTraffic
