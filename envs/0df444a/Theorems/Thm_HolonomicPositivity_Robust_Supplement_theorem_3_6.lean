-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_theorem_3_6
-- name    : HolonomicPositivity.Robust.Supplement.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:57:28.6542+00:00
-- url     : https://prove2.me/theorems/c27c93bb-21a7-484d-b86d-126acdc487b8
-- title:
--   Theorem 3.6 — positivity procedure and exact termination
-- statement:
--   There is one partial recursive procedure on finite descriptions of real-algebraic rational functions $P,Q$ and real-algebraic initial triples $v=(v_0,v_1,v_2)$. For every $P,Q$ satisfying the coefficient condition of Theorem 3.6 there is a real linear subspace $H(P,Q)\subseteq\mathbb R^3$, depending only on $P,Q$, with
--   $$\dim H(P,Q)\le2.$$
--   Let $f$ be the normalized recurrence solution with initial triple $v$. For every description of these data,
--   $$\text{the procedure halts}\quad\Longleftrightarrow\quad v\notin H(P,Q)\ \lor\ \neg(\forall n\in\mathbb N,\ f(n)>0).$$
--   Every returned Boolean is correct: it is true exactly when $f$ is positive at every natural index. The coefficient condition includes both source cases, including $P=0$ in case (1), pole-freeness on $\mathbb N$, and $Q(n)\ne0$ there.
--
--   This companion theorem gives a positivity decision procedure with the exact exceptional-subspace termination characterization, rather than merely an abstract function with no computability requirement.
--
--   Differences from the source:
--   - reading: P(x)>−1/3+O(x⁻²), with only the mirror comparison < defined explicitly → GtMod: eventual ≥ and failure of EqMod at order −2; reason: the mirror of line 166 gives exactly the II-1 or II-2 cases named in the parenthetical on p.7
--   - encoding: a positivity procedure on real-algebraic input, correct when it halts → Partrec Input →. Bool over explicit finite descriptions, with all descriptions and Boolean correctness quantified; reason: Procedure 1 and the proof on p.10 specify these algorithm and correctness semantics
--   - encoding: a subspace H(P,Q) of R³ with dimension at most two → Submodule ℝ (Fin 3 → ℝ), Module.finrank ≤ 2, quantified before descriptions and initial triples; reason: the finite-dimensional real submodule has the source dimension and depends only on P,Q
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Theorem 3.6, PDF p.7 (printed 7); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Supplement_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Supplement_Inputs

namespace HolonomicPositivity.Robust.Supplement

/-- Theorem 3.6, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF p.7,
printed XX:7; output correctness is explicit in Procedure 1 (p.8) and its proof (p.10).
The exceptional subspace depends on P,Q, never on their descriptions or the initial triple. -/
theorem theorem_3_6 :
    ∃ proc : Input →. Bool, Partrec proc ∧
      ∃ H : RatFunc ℝ → RatFunc ℝ → Submodule ℝ (Fin 3 → ℝ),
        ∀ (P Q : RatFunc ℝ), CoeffCond P Q →
          ∀ d : CoeffInput, CoeffDenotes d P Q →
            Module.finrank ℝ (H P Q) ≤ 2 ∧
            ∀ (v : Fin 3 → ℝ) (a : PolygonPack.AlgNum × PolygonPack.AlgNum × PolygonPack.AlgNum),
              InitialDenotes a v →
              ((proc (d, a)).Dom ↔
                v ∉ H P Q ∨ ¬ Positive (solutionFrom P Q (v 0) (v 1) (v 2))) ∧
              (∀ b ∈ proc (d, a), b = true ↔
                Positive (solutionFrom P Q (v 0) (v 1) (v 2))) := by sorry

end HolonomicPositivity.Robust.Supplement
