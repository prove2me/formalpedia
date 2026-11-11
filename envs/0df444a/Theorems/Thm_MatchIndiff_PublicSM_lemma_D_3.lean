-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_3
-- name    : MatchIndiff.PublicSM.lemma_D_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:58.344651+00:00
-- url     : https://prove2.me/theorems/8205f7b9-4116-4ae1-ad7f-5239697aa211
-- title:
--   Lemma D.3 — strongly (and super-) stable matchings match the same students and schools
-- statement:
--   Consider one-to-one school choice with weak rows on both sides: $n$ students with weak rows $P_i$ over the $m$ schools and schools with weak priorities $Q_h$ over the students (ties and unacceptable partners allowed on both sides). If $\mu$ and $\nu$ are both strongly stable, then
--   $$\{d:\mu(d)\ne\bot\}=\{d:\nu(d)\ne\bot\}\quad\text{and}\quad\{h:\mu(h)\ne\bot\}=\{h:\nu(h)\ne\bot\},$$
--   and the same holds for any two super-stable matchings.
--
--   It extends the rural-hospitals theorem to strong and super stability with incomplete lists; it is used for the strict-lattice step of Lemma 6.1 and for Lemma D.9.
--
--   Differences from the source:
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 82, Lemma D.3

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- Lemma D.3 (p. 82): any two strongly stable matchings of the same instance match the same
students and the same schools; hence so do any two super-stable matchings. -/
theorem lemma_D_3 {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (hP : ∀ i, IsRow (P i)) (hQ : ∀ h, IsRow (Q h)) (μ ν : Matching n m) :
    (IsStable StabKind.strong P Q μ → IsStable StabKind.strong P Q ν →
      (∀ i, (μ.toFun i).isSome = (ν.toFun i).isSome) ∧
        ∀ h, (μ.holder h).isSome = (ν.holder h).isSome) ∧
    (IsStable StabKind.super P Q μ → IsStable StabKind.super P Q ν →
      (∀ i, (μ.toFun i).isSome = (ν.toFun i).isSome) ∧
        ∀ h, (μ.holder h).isSome = (ν.holder h).isSome) := by sorry

end MatchIndiff.PublicSM
