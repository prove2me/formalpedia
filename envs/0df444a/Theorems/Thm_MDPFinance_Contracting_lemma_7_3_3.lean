-- Prove2me | Theorems.Thm_MDPFinance_Contracting_lemma_7_3_3
-- name    : MDPFinance.Contracting.lemma_7_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:46:14.897978+00:00
-- url     : https://prove2.me/theorems/528295cd-bd71-4365-b9c1-528bcbfd640d
-- title:
--   Lemma 7.3.3 — T and T_f are contractions of modulus βα_b on the bounding-function norm
-- statement:
--   Once the model has a genuine bounding function $b$ (a two-sided reward bound, Definition 7.3.1),
--   both operators $T_f$ and $T$ are Lipschitz on $(IB_b, \|\cdot\|_b)$ with constant $\beta\alpha_b$
--   — a contraction exactly when $\beta\alpha_b < 1$. Banach's fixed point theorem then gives, for a
--   fixed decision rule $f$, that $J_f$ (the value of the stationary policy $f^\infty$) is the
--   *unique* fixed point of $T_f$ in $IB_b$, obtained as the norm-limit of iterating $T_f$ from any
--   starting point. This is the technical engine behind every result of §7.3: contraction is what
--   turns the abstract existence theory of §7.1-7.2 into concrete, computable, uniquely-determined
--   solutions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 206, Lemma 7.3.3

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.Contracting

/-- Lemma 7.3.3 (Bäuerle–Rieder, p. 206, PDF 217). Suppose the Markov Decision Model has a
bounding function `b` and let `f \in F`. a) For `v,w \in IB_b` it holds: `\|T_fv-T_fw\|_b \le
\beta\alpha_b\|v-w\|_b`, `\|Tv-Tw\|_b \le \beta\alpha_b\|v-w\|_b`. b) Let `\beta\alpha_b < 1`.
Then `J_f = \lim_n T_f^ng` for all `g \in IB_b` (norm convergence), and `J_f` is the unique fixed
point of `T_f` in `IB_b`; `J_f` renders `x \mapsto (J_{\infty}^{f^\infty}(x)).toReal`, real-valued
under the contracting hypothesis. -/
theorem lemma_7_3_3 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (f : E → A)
    (hf : IsDecisionRuleOf M f) :
    (∀ v ∈ IBb b, ∀ w ∈ IBb b,
        normb b (fun x => Tf' M f v x - Tf' M f w x) ≤ M.β * αb * normb b (fun x => v x - w x)) ∧
      (∀ v ∈ IBb b, ∀ w ∈ IBb b,
        normb b (fun x => T' M v x - T' M w x) ≤ M.β * αb * normb b (fun x => v x - w x)) ∧
      (M.β * αb < 1 →
        (∀ g ∈ IBb b, Tendsto (fun n => normb b fun x =>
            (Tf' M f)^[n] g x - (Jinfpi M M.r (fun _ => f) x).toReal) atTop (𝓝 0)) ∧
          ∀ v ∈ IBb b, Tf' M f v = v → v = fun x => (Jinfpi M M.r (fun _ => f) x).toReal) := by sorry

end MDPFinance.Contracting
