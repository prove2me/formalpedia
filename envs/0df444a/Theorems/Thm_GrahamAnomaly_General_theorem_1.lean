-- Prove2me | Theorems.Thm_GrahamAnomaly_General_theorem_1
-- name    : GrahamAnomaly.General.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:04:17.440227+00:00
-- url     : https://prove2.me/theorems/d51060af-0ecb-4e93-8a26-8e26e3eeba66
-- title:
--   Theorem 1, p. 419 — the general bound on multiprocessing timing anomalies
-- statement:
--   Run the same nonempty finite set of tasks twice by Graham's list-scheduling rule. The first run has positive durations $\mu$, strict precedence order $\prec$, arbitrary priority list $L$, $n\ge1$ identical processors, and finishing time $\omega$. The second has positive durations $\mu'\le\mu$ pointwise, a relaxed order $\prec'\subseteq\prec$, arbitrary list $L'$, $n'\ge1$ processors, and finishing time $\omega'$. Then
--
--   $$\frac{\omega'}{\omega}\le 1+\frac{n-1}{n'}.$$
--
--   The inequality limits how much the finishing time can increase even when tasks are shortened, precedence is relaxed, the list is changed, and the processor count changes together.
--
--   **Formalization Note** Both runs satisfy the list-scheduling predicate. Nonempty tasks and positive durations make $\omega>0$, so the ratio has its intended meaning. The priority lists are arbitrary permutations, including lists that do not respect precedence. The tie rule for identical processor indices is omitted because it cannot change either finishing time.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 419, Theorem 1 and §3 standing setting; https://doi.org/10.1137/0117039

import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model

namespace GrahamAnomaly.General

/-- Graham's Theorem 1: shortening tasks, relaxing precedence, changing the
priority list, and changing the processor count have this bounded effect. -/
theorem theorem_1 {r n n' : ℕ} (hr : 0 < r) (hn : 0 < n) (hn' : 0 < n')
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hμ' : ∀ j, 0 < μ' j) (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (L L' : Fin r ≃ Fin r)
    (G : Schedule n μ prec) (G' : Schedule n' μ' prec')
    (hG : IsListSchedule L G) (hG' : IsListSchedule L' G') :
    G'.finish / G.finish ≤ 1 + ((n : ℝ) - 1) / n' := by sorry

end GrahamAnomaly.General
