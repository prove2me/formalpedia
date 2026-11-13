-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_3
-- name    : LocalLemmaHierarchy.Completeness.proposition_3_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:19:58.656186+00:00
-- url     : https://prove2.me/theorems/46e81f2f-ce65-4327-8d67-28d251165ad9
-- title:
--   Proposition 3.3(a)–(b) — monotone iteration and finite grouped presentations
-- statement:
--   Let $\mathcal R$ be positive local deletion option data, $q\ge0$, and $p$ nonnegative moduli. This item does not require a polynomial family represented by these data.
--
--   (a) A certificate exists exactly when the iteration $x^{(0)}=0$, $x^{(n+1)}=F_{q,p}(x^{(n)})$ converges in $[0,1)^{S_q}$. The limit is the least fixed point and lies below every certificate.
--
--   (b) A finite grouped presentation has a certificate exactly when the full memory system has one.
--
--   (Part (c), on symmetry groups with finitely many site orbits, is not part of this item.)
--
--   Differences from the source:
--   - generalization: the sites form a countable set V → V is any type (no countability assumption); reason: no step of the proofs uses countability; the statement for countable V is the special case
--   - encoding: a total order ≺_{v,a} on D_{v,a} \ {v} → a rank R.rank v a : V → ℕ injective on D_{v,a} \ {v}, with w ≺ u ↔ rank w < rank u; reason: every total order on a finite set is induced by such a rank, and only comparisons are used
--   - encoding: x ∈ [0,1)^{S_q}, a vector on the states → x : Hist R → ℝ, constrained (0 ≤ x_s < 1 and the row inequality) only at states (IsMemState); reason: every row at a state reads only states (s ★_q (a,u) is again a state), so values elsewhere are irrelevant
--   - reading: the iteration "converges in [0,1)^{S_q}" → every iterate and the limit lie in [0,1) at every state, and the iterates converge coordinatewise; reason: F_{q,p} is defined on [0,1)^{S_q}, so the iteration lives there; convergence in the product space is coordinatewise
--   - encoding: "the limit is the least fixed point" → the limit is a fixed point in [0,1)^{S_q} and lies below every fixed point in [0,1)^{S_q} (stated when a certificate exists); reason: definition of least fixed point; the limit exists exactly when a certificate exists, by the first clause
--   - reading: a finite grouped presentation "assigns finitely many types to states" → GroupedPresentation: a finite type set, a typing, rows per type, every type is the type of some state, and every state has the row of its type; reason: types are assigned to states, so every type occurs; an unused type would carry a row no state constrains
--   - generalization: the standing framework includes a polynomial family Z satisfying the deletion identity → only PosLocalDeletionRep option data are required, with no IsRepresentationOf hypothesis; reason: the proof in Appendix B.2 uses only finite nonnegative rows, their continuity and monotonicity, and agreement of grouped rows; every source representation supplies these data
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Proposition 3.3(a)–(b), printed p. 8 (PDF p. 10); proof App. B.2, printed pp. 17–18 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory

open scoped ENNReal NNReal
open Filter Topology

namespace LocalLemmaHierarchy.Completeness

/-- **Proposition 3.3 (a)–(b) (Monotone iteration and finite presentations)**, printed p. 8 / PDF 10
(proof App. B.2, printed 17–18 / PDF 19–20). (a) A certificate exists exactly when the iteration
`x^(0) = 0`, `x^(n+1) = F_{q,p}(x^(n))` converges in `[0,1)^{S_q}`; the limit is the least fixed
point and lies below every certificate. (b) A finite grouped presentation has a certificate exactly
when the full memory system has one. Part (c) is not part of this item. -/
theorem proposition_3_3 {V T : Type} (R : PosLocalDeletionRep V T) (q : ℕ) (p : T → ℝ)
    (hp : ∀ τ, 0 ≤ p τ) :
    ((∃ x : Hist R → ℝ, IsMemCertificate R q p x) ↔
      ((∀ n s, IsMemState R q s → 0 ≤ memIter R q p n s ∧ memIter R q p n s < 1) ∧
        ∃ L : Hist R → ℝ, ∀ s, IsMemState R q s →
          0 ≤ L s ∧ L s < 1 ∧ Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s)))) ∧
    (∀ L : Hist R → ℝ, (∃ x : Hist R → ℝ, IsMemCertificate R q p x) →
      (∀ s, IsMemState R q s → Tendsto (fun n => memIter R q p n s) atTop (𝓝 (L s))) →
      (∀ s, IsMemState R q s → memUpdate R q p L s = L s ∧ 0 ≤ L s ∧ L s < 1) ∧
      (∀ y : Hist R → ℝ,
        (∀ s, IsMemState R q s → memUpdate R q p y s = y s ∧ 0 ≤ y s ∧ y s < 1) →
        ∀ s, IsMemState R q s → L s ≤ y s) ∧
      (∀ x : Hist R → ℝ, IsMemCertificate R q p x → ∀ s, IsMemState R q s → L s ≤ x s)) ∧
    ∀ P : GroupedPresentation R q p,
      (∃ y : P.Θ → ℝ, P.IsCertificate y) ↔ ∃ x : Hist R → ℝ, IsMemCertificate R q p x := by sorry

end LocalLemmaHierarchy.Completeness
