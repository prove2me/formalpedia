-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_6_9
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:05:59.096917+00:00
-- url     : https://prove2.me/theorems/5fd5c94b-9e63-4cbd-8dd2-649ccd01673d
-- title:
--   Proposition 6.9 — The explicit WalkSAT tail lower bound and its exponential-mean consequence
-- statement:
--   For a graph $G$ satisfying the §6 graph conditions, let $N=|V|$, $\rho=451/486$, $\gamma=\tfrac18\log_2(1/\rho)>0$ and $K_N=\lfloor2^{\gamma N}\rfloor$. Set $N_0=\lceil\max(2\ln4,\log_2(4\cdot486/451)/\gamma)\rceil$. With uniform clause selection and independent uniform initialization, every such graph with $N\ge N_0$ satisfies
--
--   $$P(T_{WS}\ge K_N)\ge1-\exp(-N/2)-\frac{486}{451}2^{-\gamma N},$$
--   $$E[T_{WS}]\ge2^{\gamma N-2}.$$
--
--   Thus the expectation has the stated exponential lower bound. The explicit sufficient threshold and the mean estimate are supplied by the error and floor estimates in the proof on pp. 42–43; no finiteness assumption is imposed.
--
--   Differences from the source:
--   - generalization: G is a graph of the explicitly constructed family in Lemma 6.2 → any finite simple connected 102-regular graph with λ₁=102 and every other adjacency eigenvalue of absolute value less than 21; reason: every graph in the source family satisfies exactly these conditions; the proofs use only these graph properties
--   - encoding: vertices, indexed gadget clauses and Boolean assignments → vertices Fin N, finite sum/product index types and Bool-valued assignments including every auxiliary bit; reason: finite bijective labels change no instance and both orientations of each edge are retained
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
--   - encoding: for all sufficiently large |V|, with exponential mean consequence → the explicit sufficient threshold N₀ and bound E[T_WS]≥2^(γN−2) from pp. 42–43; reason: the first error is at most 1/4 and the second at most 1/4 at this threshold; 2^(γN)≥2 permits the floor estimate, so the full eventual assertion follows
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 6.9, p. 42; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_6_9 {N : ℕ} (G : SimpleGraph (Fin N)) (hG : GoodGraph G)
    (hN : separationThreshold ≤ N) :
    0 < gamma ∧
    ENNReal.ofReal (1-Real.exp (-(N:ℝ)/2)-(486/451:ℝ)*(2:ℝ)^(-gamma*N)) ≤
      wsLaw (expFormula G) (uniformRuleWS (expFormula G)) (uniformAssignment (ExpVar N))
        {ω | (barrierTime N : ℕ∞) ≤ wsTimeOf (expFormula G) ω} ∧
    ENNReal.ofReal ((2:ℝ)^(gamma*N-2)) ≤
      wsExpectedTime (expFormula G) (uniformRuleWS (expFormula G))
        (uniformAssignment (ExpVar N)) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
