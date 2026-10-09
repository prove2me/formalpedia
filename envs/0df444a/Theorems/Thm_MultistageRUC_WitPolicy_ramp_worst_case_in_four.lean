-- Prove2me | Theorems.Thm_MultistageRUC_WitPolicy_ramp_worst_case_in_four
-- name    : MultistageRUC.WitPolicy.ramp_worst_case_in_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:04.358967+00:00
-- url     : https://prove2.me/theorems/231aae11-dfb8-4be7-a11b-6b3ff08d1588
-- title:
--   Proposition 6, proof of (ii), (25a)–(25d), p. 19 — the worst-case ramp is attained at one of four extreme scenarios
-- statement:
--   Let $\mathcal D$ be the budget uncertainty set (3), and let $\mathbf d_{\max},\mathbf d_{\min}\in\mathcal D$ maximize, respectively minimize, the total load of every period over $\mathcal D$ ((19), (20)). Fix a generator $i$, coefficients $W_{it}$, and two consecutive periods $t-1$, $t$. For a trajectory $\mathbf d$ write
--   $$f(\mathbf d)=W_{it}\sum_{j\in\mathcal N_d}d^t_j-W_{i,t-1}\sum_{j\in\mathcal N_d}d^{t-1}_j .$$
--   Let $\mathcal S_t=\{\mathbf d_{\min},\mathbf d_{\max},\mathbf d_{minmax}(t),\mathbf d_{maxmin}(t)\}$ with the scenarios (21)–(22). Then for every $\mathbf d\in\mathcal D$:
--   1. there is $\mathbf d'\in\mathcal S_t$ with $f(\mathbf d)\le f(\mathbf d')$;
--   2. there is $\mathbf d''\in\mathcal S_t$ with $f(\mathbf d'')\le f(\mathbf d)$.
--
--   So both the maximum and the minimum of $f$ over $\mathcal D$ are attained in the four-element set $\mathcal S_t$. Which scenario is extremal depends on the signs of $W_{it}$ and $W_{i,t-1}$ (the four cases (25a)–(25d) of the paper). The maximum governs the ramping-up constraints (8e), the minimum the ramping-down constraints (8d).
--
--   **Formalization Note.** Lean periods are 0-based and are indices `s`, `t` with `t = s + 1`. The scenarios $\mathbf d_{minmax}(t)$, $\mathbf d_{maxmin}(t)$ are defined exactly by (21)–(22): $\mathbf d_{minmax}(t)$ has period $t$ from $\mathbf d_{\max}$ and period $t-1$ from $\mathbf d_{\min}$. The page's assignment of the labels (25a) and (25d) to these scenarios is swapped; the statement, which quantifies over the whole four-element set, is unaffected.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 19, Proof of Proposition 6, (25a)–(25d)

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

namespace MultistageRUC.WitPolicy

theorem ramp_worst_case_in_four {Ng Nd T : ℕ}
    (W : Fin Ng → Fin T → ℝ) (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin)
    (i : Fin Ng) (s t : Fin T) (hst : t.val = s.val + 1) :
    ∀ d ∈ MultistageRUC.Equiv.uncSet dbar dhat Γ,
      (∃ d' ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
          Set (Fin T → Fin Nd → ℝ)),
        W i t * totalLoad d t - W i s * totalLoad d s ≤
          W i t * totalLoad d' t - W i s * totalLoad d' s) ∧
      (∃ d' ∈ ({dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} :
          Set (Fin T → Fin Nd → ℝ)),
        W i t * totalLoad d' t - W i s * totalLoad d' s ≤
          W i t * totalLoad d t - W i s * totalLoad d s) := by sorry

end MultistageRUC.WitPolicy
