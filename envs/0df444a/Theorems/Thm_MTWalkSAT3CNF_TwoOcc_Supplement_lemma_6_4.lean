-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_Supplement_lemma_6_4
-- name    : MTWalkSAT3CNF.TwoOcc.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:04:29.729442+00:00
-- url     : https://prove2.me/theorems/67bed576-f41d-470b-9f34-dc927d526d6f
-- title:
--   Lemma 6.4 — All properties of the expander formula, including counts, occurrences and the satisfying-set characterization
-- statement:
--   For a graph $G$ satisfying the §6 graph conditions, let $N=|V|$ and construct $F(G)$ using all the indexed gadgets and both orientations of each edge. Every clause has three distinct variables and is non-tautological. The counts and occurrence bound are
--
--   $$n=823N,\qquad m=1846N,\qquad\Delta(F(G))\le1740.$$
--
--   For every complete assignment $x$, including all auxiliary bits,
--
--   $$B(x)=717|Z_0(x)|+52|Z_1(x)|+2e_G(S(x),Z_0(x))+e_G(S(x),Z_1(x)).$$
--
--   Furthermore, $x$ satisfies $F(G)$ if and only if $S(x)=V$. Here $S,Z_0,Z_1$ are the active, zero-progress and one-progress block sets, and crossing edges are counted once. All clauses of the source lemma are included.
--
--   Differences from the source:
--   - generalization: G is a graph of the explicitly constructed family in Lemma 6.2 → any finite simple connected 102-regular graph with λ₁=102 and every other adjacency eigenvalue of absolute value less than 21; reason: every graph in the source family satisfies exactly these conditions; the proofs use only these graph properties
--   - encoding: vertices, indexed gadget clauses and Boolean assignments → vertices Fin N, finite sum/product index types and Bool-valued assignments including every auxiliary bit; reason: finite bijective labels change no instance and both orientations of each edge are retained
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), Lemma 6.4, p. 36–37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc.Supplement

theorem lemma_6_4 {N : ℕ} (G : SimpleGraph (Fin N)) (hG : GoodGraph G) :
    (∀ i, Function.Injective ((expFormula G) i).var ∧
      ¬ ∃ p q, ((expFormula G) i).var p = ((expFormula G) i).var q ∧
        ((expFormula G) i).sign p ≠ ((expFormula G) i).sign q) ∧
    Fintype.card (ExpVar N) = 823*N ∧
    Fintype.card (ExpIndex G) = 1846*N ∧
    numOccVars (expFormula G) = 823*N ∧
    (∀ v, occCount (expFormula G) v ≤ 1740) ∧
    (∀ x : ExpVar N → Bool,
      (bad (expFormula G) x).card = 717*(zeroBlocks x).card + 52*(oneBlocks x).card +
        2*cutCount G (active x) (zeroBlocks x) + cutCount G (active x) (oneBlocks x)) ∧
    (∀ x : ExpVar N → Bool, bad (expFormula G) x = ∅ ↔ active x = Finset.univ) := by sorry

end MTWalkSAT3CNF.TwoOcc.Supplement
