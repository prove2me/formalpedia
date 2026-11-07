-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_2_5
-- name    : GSRandomOrder.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:34.825265+00:00
-- url     : https://prove2.me/theorems/9c73b7b4-31fa-4578-9e6d-83ad2d4aee31
-- title:
--   Lemma 2.5 — the domain of a GS valuation is a matroid
-- statement:
--   Let $v$ be a GS valuation on $N$. Then $\operatorname{dom}v=\{S: v(S)>-\infty\}$ is the family of independent sets of a matroid on $N$.
--
--   So the feasible sets of a GS valuation always form a matroid, and the GS secretary problem contains the matroid secretary problem.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: a matroid on N → a Mathlib Matroid (Fin n) with ground set univ whose independent finite sets S are exactly those with v S ≠ ⊥; reason: Lean's matroid structure on a finite ground set
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma 2.5, p.6 (proof in Appendix A, p.21)

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma 2.5 (Matroid domain)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.1, p.6; proof in App. A, p.21).
If `v` is a GS valuation, then `dom v` is the family of independent sets of a matroid on `N`.

**Formalization Note.** "A matroid on `N`" is a Mathlib `Matroid (Fin n)` with ground set all of
`Fin n`; its independent sets are exactly the (finite) sets `S` with `v S ≠ ⊥`. -/
theorem lemma_2_5 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v) :
    ∃ M : Matroid (Fin n), M.E = Set.univ ∧
      ∀ S : Finset (Fin n), M.Indep (S : Set (Fin n)) ↔ v S ≠ ⊥ := by sorry

end GSRandomOrder
