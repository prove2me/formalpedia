-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_proposition_3_5
-- name    : JainCRERepetition.Cubic.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:36.959464+00:00
-- url     : https://prove2.me/theorems/b624d83d-6719-4111-95d3-7ed46f8fd7af
-- title:
--   Proposition 3.5 — full workspace budget for a repeated strategy
-- statement:
--   Fix an actual repeated strategy, its coherent local representation, a proper checked set $C$ and $p_C>0$. The constructed coordinate vectors are normalized consistent full-workspace targets, and satisfy the coherent copied-input expansion. Their comparisons are precisely the prescribed conditional marginals with the target history weights. Both comparisons are conditional comparisons and their full divergences are finite. With $m=|[n]\setminus C|$ and $t=B_C/m$,
--
--   $$\frac1m\sum_{i\notin C}(b_{A,i}+b_{B,i})\le2t,\qquad\frac1m\sum_{i\notin C}D(q_i\|\mu)\le t.$$
--
--   The workspaces, histories and comparisons are computed before any fresh questions arrive. The two bounds control different errors and neither is a hypothesis of this proposition.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - encoding: retained local measurement outputs and checked answer copies → coherently copy every answer and place unchecked copies in the retained local environment; reason: this is a fixed local isometry with a local inverse on its image; it preserves every source instance, charge and designated answer law
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 25, Proposition 3.5, Eq. (30); pp. 23–24, Eqs. (25)–(29); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_repeated

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem proposition_3_5
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
    {n : ℕ} {G : QuantumParallelRepetition.Game X Y A B}
    (S : QuantumParallelRepetition.Strategy (G.repeat n)) (T : CoherentStrategy S)
    (C : Finset (Fin n)) (hC : C ≠ Finset.univ) (hp : 0 < checkedProbability S C) :
    (∀ i ∈ unchecked C,
      coordinateConsistent T C i ∧ coordinateExpansion T C i ∧
      IsState (coordinateComparison T C i true) ∧ IsState (coordinateComparison T C i false) ∧
      RegComparison (regType T) (.xh i) (.x i) (.yh i) (Equiv.refl X) (priorLaw G)
        (coordinateComparison T C i true) ∧
      RegComparison (regType T) (.yh i) (.y i) (.xh i) (Equiv.refl Y) (swapLaw (priorLaw G))
        (coordinateComparison T C i false) ∧
      FiniteD (coordinateTarget T C i true) (coordinateComparison T C i true) ∧
      FiniteD (coordinateTarget T C i false) (coordinateComparison T C i false)) ∧
    (∑ i ∈ unchecked C, coordinateS T C i) / (unchecked C).card ≤ 2 * budgetRatio S C ∧
    (∑ i ∈ unchecked C, classicald (coordinateLaw S C i) (priorLaw G).p) /
      (unchecked C).card ≤ budgetRatio S C := by sorry
end JainCRERepetition.Cubic
