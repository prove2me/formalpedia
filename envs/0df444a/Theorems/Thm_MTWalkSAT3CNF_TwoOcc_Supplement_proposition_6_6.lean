-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_proposition_6_6
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.proposition_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:05:13.435204+00:00
-- url     : https://prove2.me/theorems/e07e984a-9b14-47ef-8a69-826ba444a859
-- title:
--   Proposition 6.6 — Every MT hitting-time bound: fixed initialization, both uniform mean bounds and the uniform tail
-- statement:
--   For $G$ satisfying the §6 graph conditions, write $N=|V|$ and use uniform clause selection in MT on $F(G)$. For every fixed initial assignment $\sigma$, with active set $S(\sigma)$,
--
--   $$E_\sigma[T_{MT}]\le3684(N-|S(\sigma)|).$$
--
--   Under independent uniform initialization of every variable, including auxiliary bits,
--
--   $$\frac{3N}{4}\le E[T_{MT}]\le2763N,\qquad P(T_{MT}>7368N)\le\exp(-N/58944).$$
--
--   The mean lower bound, mean upper bound and tail estimate are all retained. The fixed-initialization statement uses the published step kernel with a Dirac initial law.
--
--   Differences from the source:
--   - generalization: G is a graph of the explicitly constructed family in Lemma 6.2 → any finite simple connected 102-regular graph with λ₁=102 and every other adjacency eigenvalue of absolute value less than 21; reason: every graph in the source family satisfies exactly these conditions; the proofs use only these graph properties
--   - encoding: vertices, indexed gadget clauses and Boolean assignments → vertices Fin N, finite sum/product index types and Bool-valued assignments including every auxiliary bit; reason: finite bijective labels change no instance and both orientations of each edge are retained
--   - encoding: possibly infinite algorithmic hitting times and expectations → published ℕ∞ hitting times and ℝ≥0∞ lower integrals; finite real bounds embedded by ENNReal.ofReal; reason: preserves infinite runtimes and is equivalent to each displayed nonnegative bound
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Proposition 6.6, p. 39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem proposition_6_6 {N : ℕ} (G : SimpleGraph (Fin N)) (hG : GoodGraph G) :
    (∀ σ : ExpVar N → Bool,
      mtMeanFrom (expFormula G) (uniformRuleMT (expFormula G)) σ ≤
        ENNReal.ofReal (3684*((N:ℝ)-(active σ).card))) ∧
    ENNReal.ofReal (3*(N:ℝ)/4) ≤
      (cnfSystem (expFormula G)).expectedTime (uniformRuleMT (expFormula G)) ∧
    (cnfSystem (expFormula G)).expectedTime (uniformRuleMT (expFormula G)) ≤
      ENNReal.ofReal (2763*(N:ℝ)) ∧
    (cnfSystem (expFormula G)).mtLaw (uniformRuleMT (expFormula G))
      {ω | (7368*N : ℕ∞) < (cnfSystem (expFormula G)).mtTimeOf ω} ≤
        ENNReal.ofReal (Real.exp (-(N:ℝ)/58944)) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
