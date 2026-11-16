-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_5_1
-- name    : OddPermSum.Evaluation.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:03.150701+00:00
-- url     : https://prove2.me/theorems/0c0dceae-897c-47ff-ab64-a9bca8f70c44
-- title:
--   Lemma 5.1 (used in the proof of Theorem 1.2) — Cycle polynomial and lowest coefficient
-- statement:
--   Let $D$ be a loopless simple directed graph, and let $Q(z,w)=\Phi(I+zW(w))$ over a characteristic-two field. If $D$ has no even directed cycle, then $Q=0$. Otherwise let $\ell$ be its shortest even-cycle length, and let $\mathcal C_\ell$ be all cycles of that length. Then
--   $$[z^r]Q=0\ (r<\ell),\qquad [z^\ell]Q=\sum_{C\in\mathcal C_\ell}\prod_{e\in E(C)}w_e\ne0.$$
--   Nonvanishing concerns a formal polynomial in independent arc variables. This identifies the first possible nonzero degree without a genericity assumption on an evaluated weight assignment.
--
--   Differences from the source:
--   - encoding: vertices indexed by [n] and cycles up to rotation → vertices indexed by Fin n and cycles represented by their directed arc sets; reason: zero-based relabeling and rotation quotient preserve every directed cycle, including length two
--   - generalization: the field F_{2^d} chosen for the graph application → every field of characteristic two; reason: the coefficient identities and deterministic extraction are field-independent and include the chosen finite fields
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 13, Lemma 5.1

import Definitions.Def_OddPermSum_Evaluation_Supplement_generatingPolynomial

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_5_1 {F : Type*} [Field F] [CharP F 2] {n : ℕ} (D : Digraph n) :
    ((evenCycles D = ∅) → generatingQ (F := F) D = 0) ∧
    (∀ ℓ, IsShortest D ℓ →
      (∀ r < ℓ, (generatingQ (F := F) D).coeff r = 0) ∧
      (generatingQ (F := F) D).coeff ℓ = ∑ C ∈ cyclesAt D ℓ, cycleMonomial (F := F) D C ∧
      (generatingQ (F := F) D).coeff ℓ ≠ 0) := by sorry

end OddPermSum.Evaluation.Supplement
