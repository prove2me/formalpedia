-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_14
-- name    : MatchIndiff.PublicSM.lemma_D_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:42.756308+00:00
-- url     : https://prove2.me/theorems/82012672-6769-48d9-8186-23d58c75b724
-- title:
--   Lemma D.14 — strongly stable matchings with equal student ranks; super-stable ones are equal
-- statement:
--   In one-to-one school choice with weak rows on both sides, let $\mu,\nu$ be strongly stable and give every student the same rank, $\mathrm{rk}_d(\mu(d);P_d)=\mathrm{rk}_d(\nu(d);P_d)$ for all $d$. Then they match the same students and the same schools, and at every occupied school the two holders are tied in the public priority:
--   $$\mathrm{rk}_h(\mu(h);Q_h)=\mathrm{rk}_h(\nu(h);Q_h).$$
--   If $\mu,\nu$ are super stable, equality of all student ranks implies $\mu=\nu$.
--
--   It reduces exact verification to rank verification: within a rank class only tied holders can be exchanged, and none for super stability.
--
--   Differences from the source:
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 97, Lemma D.14

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- Lemma D.14 (p. 97): two strongly stable matchings giving every student the same rank match
the same students and schools, and their holders at every occupied school are tied in the public
priority; two super-stable matchings with equal student ranks are equal. -/
theorem lemma_D_14 {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (hP : ∀ i, IsRow (P i)) (hQ : ∀ h, IsRow (Q h)) (μ ν : Matching n m) :
    (IsStable StabKind.strong P Q μ → IsStable StabKind.strong P Q ν →
      (∀ i, rk (P i) (μ.toFun i) = rk (P i) (ν.toFun i)) →
      ((∀ i, (μ.toFun i).isSome = (ν.toFun i).isSome) ∧
        (∀ h, (μ.holder h).isSome = (ν.holder h).isSome) ∧
        ∀ h, (μ.holder h).isSome → rk (Q h) (μ.holder h) = rk (Q h) (ν.holder h))) ∧
    (IsStable StabKind.super P Q μ → IsStable StabKind.super P Q ν →
      (∀ i, rk (P i) (μ.toFun i) = rk (P i) (ν.toFun i)) → μ = ν) := by sorry

end MatchIndiff.PublicSM
