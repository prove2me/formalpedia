-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_9
-- name    : MatchIndiff.PublicSM.lemma_D_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:50.275355+00:00
-- url     : https://prove2.me/theorems/17cf4352-7213-42ef-869b-7d0382d27347
-- title:
--   Lemma D.9 — a nonempty strong or super stable set has a school-best matching
-- statement:
--   In one-to-one school choice with weak rows on both sides, fix $\alpha\in\{\text{strong},\text{super}\}$ and suppose some $\alpha$-stable matching exists. Then there is an $\alpha$-stable $\mu$ that is *school-best*: every school weakly prefers its holder in $\mu$ to its holder in every other $\alpha$-stable matching,
--   $$\mathrm{rk}_h(\mu(h);Q_h)\le \mathrm{rk}_h(\nu(h);Q_h)\quad\text{for all }\alpha\text{-stable }\nu\text{ and all schools }h.$$
--   Only priority ranks matter; tied holders need not be unique. The side-reversed argument gives a student-best matching, used in Lemma D.19 and in Lemma 6.1.
--
--   Differences from the source:
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
--   - encoding: α ∈ {strong, super} → α : StabKind with α ≠ weak; reason: Lean convention; the two cases
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 90, Lemma D.9

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- Lemma D.9 (p. 90): for strong or super stability, if the stable set is nonempty it contains a
school-best matching: every school weakly prefers its holder to its holder in every stable
matching. -/
theorem lemma_D_9 {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (hP : ∀ i, IsRow (P i)) (hQ : ∀ h, IsRow (Q h)) (α : StabKind) (hα : α ≠ StabKind.weak)
    (hne : ∃ μ : Matching n m, IsStable α P Q μ) :
    ∃ μ : Matching n m, IsStable α P Q μ ∧
      ∀ ν : Matching n m, IsStable α P Q ν → ∀ h, rk (Q h) (μ.holder h) ≤ rk (Q h) (ν.holder h) := by sorry

end MatchIndiff.PublicSM
