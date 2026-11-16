-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_5_2
-- name    : OddPermSum.Evaluation.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:53.763516+00:00
-- url     : https://prove2.me/theorems/319446f2-ca00-4772-bc7e-2b693488e6b3
-- title:
--   Lemma 5.2 (used in the proof of Theorem 1.2) — Arc-derivative support
-- statement:
--   Let $D$ have shortest even-cycle length $\ell$. For each arc $e$, set $Q_e=w_e\partial Q/\partial w_e$, with formal differentiation. Then
--   $$[z^\ell]Q_e=\sum_{C\in\mathcal C_\ell,\ e\in E(C)}\prod_{f\in E(C)}w_f,\qquad [z^\ell]Q_e\ne0\ \Longleftrightarrow\ e\in E_\ell.$$
--   Here $E_\ell$ is the full union of arcs of shortest even directed cycles. The equivalence identifies every support arc, rather than selecting one cycle.
--
--   Differences from the source:
--   - encoding: vertices indexed by [n] and cycles up to rotation → vertices indexed by Fin n and cycles represented by their directed arc sets; reason: zero-based relabeling and rotation quotient preserve every directed cycle, including length two
--   - generalization: the field F_{2^d} chosen for the graph application → every field of characteristic two; reason: the coefficient identities and deterministic extraction are field-independent and include the chosen finite fields
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 13, Lemma 5.2

import Definitions.Def_OddPermSum_Evaluation_Supplement_generatingPolynomial

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_5_2 {F : Type*} [Field F] [CharP F 2] {n : ℕ}
    (D : Digraph n) (ℓ : ℕ) (hℓ : IsShortest D ℓ) (e : D.Arc) :
    (arcQ (F := F) D e).coeff ℓ =
      ∑ C ∈ (cyclesAt D ℓ).filter (fun C => e.val ∈ C), cycleMonomial (F := F) D C ∧
    ((arcQ (F := F) D e).coeff ℓ ≠ 0 ↔ e.val ∈ shortestArcs D ℓ) := by sorry

end OddPermSum.Evaluation.Supplement
