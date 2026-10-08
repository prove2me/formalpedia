-- Prove2me | Theorems.Thm_OnlineTaxiRouting_Integrality_relax_eq_flow_of_fixed
-- name    : OnlineTaxiRouting.Integrality.relax_eq_flow_of_fixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:45.698399+00:00
-- url     : https://prove2.me/theorems/e78be04c-705e-4a96-94c5-8df4c57cf1ac
-- title:
--   §3.2, proof of Theorem 1, p. 13 — with fixed times the relaxation is the flow system (6)–(11) without the forced-zero arcs
-- statement:
--   Consider a taxi routing instance with fixed pick-up times $t^{\min}_c = t^{\max}_c =: t^*_c$ for all customers $c$. Let
--   $$A = \{(c', c) : T_{c',c} \le t^*_c - t^*_{c'}\}, \qquad B = \{(k, c) : t^{\mathrm{init}}_k + T_{k,c} \le t^*_c\}.$$
--   Then a point $(x, y, p, t)$ lies in the LP relaxation of (5)–(14) if and only if $t = t^*$ and $(x, y, p)$ lies in the relaxed network-flow system (6)–(11) on the arc subset $A \cup B$, i.e. satisfies (6)–(8), $0 \le x, y, p \le 1$, $x_{c',c} = 0$ for $(c',c) \notin A$ and $y_{k,c} = 0$ for $(k,c) \notin B$.
--
--   In words: with fixed times, (13) forces $x_{c',c} = 0$ exactly when $T_{c',c} - (t^*_c - t^*_{c'}) > 0$ and is otherwise inactive; the same reasoning applied to (14) forces $y_{k,c} = 0$ exactly when $t^{\mathrm{init}}_k + T_{k,c} - t^*_c > 0$. This is the second step of the proof of Theorem 1: the feasible region in $(x, y, p)$ is that of the network-flow constraints with some variables removed.
--
--   **Formalization Note** The standing acyclicity assumption of §2.1 is not needed and is omitted. The page states the taxi-arc case only as "the same reasoning applies to Constraint (14)"; the set $B$ above is that reasoning written out.
-- source:
--   Bertsimas–Jaillet–Martin, accepted manuscript (March 2018), §3.2, proof of Theorem 1, p. 13

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting

namespace OnlineTaxiRouting.Integrality

theorem relax_eq_flow_of_fixed {C K : Type*} [Fintype C] [Fintype K]
    (I : Instance C K) (hfix : ∀ c, I.tmin c = I.tmax c) :
    relax I = {v | (v.1, v.2.1, v.2.2.1) ∈
        flowRelax (fun c' c => I.T c' c ≤ I.tmin c - I.tmin c')
          (fun k c => I.tinit k + I.Tk k c ≤ I.tmin c) ∧
      v.2.2.2 = I.tmin} := by sorry

end OnlineTaxiRouting.Integrality
