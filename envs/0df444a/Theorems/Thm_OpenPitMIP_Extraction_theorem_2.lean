-- Prove2me | Theorems.Thm_OpenPitMIP_Extraction_theorem_2
-- name    : OpenPitMIP.Extraction.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:49.638913+00:00
-- url     : https://prove2.me/theorems/ca480acf-351c-4e0c-8830-1a5718c02351
-- title:
--   Theorem 2, p. 1432 — early start cuts: w_{c,t} = 0 for PCPSP-F and w_{c,t} ≤ (Q_t − q(cl(c)∖{c}))⁺/q_c for PCPSP-P
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions. Let $t\in\mathcal T$, $Q_t=\sum_{t'=1}^{t}U_{t'}$, and let $c\in\mathcal C$ be a cluster with
--   $$q(cl(c))>Q_t .$$
--   Then:
--
--   1. the equality $w_{c,t}=0$ holds at every point feasible for the PCPSP-F that satisfies the mining capacity rows (8);
--   2. if $q_c=q(\{c\})>0$, the inequality
--   $$w_{c,t}\le\frac{\bigl(Q_t-q(cl(c)\setminus\{c\})\bigr)^+}{q_c},\qquad (a)^+=\max\{0,a\},$$
--   holds at every point feasible for the PCPSP-P that satisfies (8).
--
--   Early start cuts fix variables to zero or tighten their upper bound before the solve, and so can serve as preprocessing.
--
--   **Formalization Note** "Valid for PCPSP-F/P" is stated as: for every feasible point of the formulation with the given integrality condition whose mining capacity rows (8) hold, the inequality holds at $w=\sum_{t'\le t}x_{\cdot,t'}$. The paper calls the first item known (Gaupp 2008); it is part of the statement here.
-- source:
--   Oper. Res. 68(5), Theorem 2, p. 1432

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace OpenPitMIP.Extraction

/-- Theorem 2 (early start cuts), p. 1432. If `q(cl(c)) > Q_t`, then `w_{c,t} = 0` is valid for
the PCPSP-F, and, when `q_c > 0`, `w_{c,t} ≤ (Q_t − q(cl(c) \ {c}))⁺ / q_c` is valid for the
PCPSP-P. "Valid" means: at every feasible point whose mining capacity rows (8) hold. -/
theorem theorem_2 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [DecidableEq C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (t : Fin T) (c : C)
    (hc : I.Qcum t < I.qSet (I.cl c)) :
    (∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .F x y → I.MiningCap y → PCPSPC.cum x c t = 0) ∧
    (0 < I.qSet {c} →
      ∀ (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ),
        I.Feasible .P x y → I.MiningCap y →
          PCPSPC.cum x c t ≤ max 0 (I.Qcum t - I.qSet (I.cl c \ {c})) / I.qSet {c}) := by sorry

end OpenPitMIP.Extraction
