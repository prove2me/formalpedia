-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_lemma_3
-- name    : MonopolyDemandUncertainty.SBSMP.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:14.45499+00:00
-- url     : https://prove2.me/theorems/8e905c94-66b1-40b1-bb2d-a0a54970d5c5
-- title:
--   Lemma 3, p. 4 (PDF 5), with v_ < v*_i, in the form its proof shows (false as printed at v*_i = v_)
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1 and 2. Let $(x,t)$ be a deterministic BIC and EIR mechanism and $i \in \{1,2\}$. Suppose $V_i$ (the types consuming in state $i$ only) is nonempty, with infimum $v_i^* = \inf V_i$, and suppose
--
--   1. $\underline v < v_i^*$, and
--   2. every type $v \in V$ with $v < v_i^*$ consumes in neither state.
--
--   Then every type of $V_i$ pays $v_i^*$ in state $i$:
--   $$t_i(v) = v_i^* \qquad \text{for all } v \in V_i.$$
--
--   Lemma 3 pins down the price faced by $V_i$: it is the valuation of its lowest member, as in a posted-price mechanism.
--
--   **Formalization Note** The page states the lemma under case hypotheses ("$V_1$ and $V_2$ both nonempty with $v_i^* < v_j^*$, or only $V_i$ and $V_{12}$ nonempty with $v_i^* < v_{12}^*$"), whose proof begins "valuations less than $v_i^*$ belong to $V_\emptyset$". That sentence is hypothesis 2 here. Hypothesis 1 is added: as printed the lemma is false when $v_i^* = \underline v > 0$ (posted prices $0$ in state 1 on $[\underline v, b)$ and $b$ in state 2 on $[b,\bar v]$ are BIC and EIR with $t_1 \equiv 0 \ne v_1^*$). The conclusion is stated on $V_i$, because $t_i(v_i^*)$ is meaningless when $v_i^* \notin V_i$.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 4, Lemma 3 (with proof)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Lemma 3, p. 4 (PDF 5), in the form its proof shows: if `V_i` is nonempty with infimum
`v_i* > v_` and every type of `V` below `v_i*` consumes in neither state, then BIC, EIR and
Conditions 1–2 force `t_i(v) = v_i*` for every `v ∈ V_i`. (As printed, without `v_ < v_i*`, the
lemma is false when `v_i* = v_ > 0`.) -/
theorem lemma_3 (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M) (i : Fin 2)
    (hne : (E.onlySet M i).Nonempty) (hlo : E.vlo < sInf (E.onlySet M i))
    (hbelow : ∀ v ∈ E.V, v < sInf (E.onlySet M i) → ∀ j, M.x j v = false) :
    ∀ v ∈ E.onlySet M i, M.t i v = sInf (E.onlySet M i) := by sorry
end MonopolyDemandUncertainty.SBSMP
