-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_6_1
-- name    : OddPermSum.Evaluation.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:52.137001+00:00
-- url     : https://prove2.me/theorems/9bba0691-5c7c-4298-ab26-21280c938c9b
-- title:
--   Lemma 6.1 (used in the proof of Theorem 1.3) — Deterministic extraction correctness
-- statement:
--   Fix a loopless simple digraph $D$, any characteristic-two field $F$, any weight assignment $\beta\in F^E$, and complete vertex and arc orders. Suppose that the candidate length $r$ equals the shortest even-cycle length $\ell$ and that an initial arc coefficient $\alpha_e=[z^r](z\beta_eG(I+zW_\beta)_{v,u})$ is nonzero. Then the specified extraction function returns a verified simple directed cycle of length exactly $\ell$ after exactly
--   $$\ell-1$$
--   extensions following the initial arc. There is no randomness or genericity hypothesis on $\beta$.
--
--   The assertion concerns the pure procedure of §6.1, including its actual choices and failure checks; its time-efficient implementation is the subject of the companion theorem.
--
--   Differences from the source:
--   - encoding: vertices indexed by [n] and cycles up to rotation → vertices indexed by Fin n and cycles represented by their directed arc sets; reason: zero-based relabeling and rotation quotient preserve every directed cycle, including length two
--   - generalization: the field F_{2^d} chosen for the graph application → every field of characteristic two; reason: the coefficient identities and deterministic extraction are field-independent and include the chosen finite fields
--   - encoding: execution over R_r and a selected initial arc with nonzero coefficient → full-polynomial pure execution and existence of a nonzero initial coefficient; reason: all degree-r tests commute with truncation and a complete arc order selects a nonzero initial arc exactly when one exists
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 18, Lemma 6.1

import Definitions.Def_OddPermSum_Evaluation_Supplement_extraction

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_6_1 {F : Type*} [Field F] [CharP F 2] {n : ℕ}
    (D : Digraph n) (ord : ExtractionOrders D) (β : D.Arc → F)
    (ℓ r : ℕ) (hℓ : IsShortest D ℓ) (hr : r = ℓ)
    (hα : ∃ e : D.Arc, initialCoefficient D β r e ≠ 0) :
    ∃ p, extract D ord β r = (some p,ℓ-1) ∧ ValidCycle D ℓ p := by sorry

end OddPermSum.Evaluation.Supplement
