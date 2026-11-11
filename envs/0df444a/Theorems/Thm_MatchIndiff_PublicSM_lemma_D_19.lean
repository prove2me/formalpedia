-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_19
-- name    : MatchIndiff.PublicSM.lemma_D_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:51.972771+00:00
-- url     : https://prove2.me/theorems/3ad3e94e-2e35-4489-9557-15fa0b5b1042
-- title:
--   Lemma D.19 — optimal student ranks iff no improvement
-- statement:
--   In one-to-one school choice with weak rows on both sides, fix $\alpha\in\{\text{strong},\text{super}\}$ and an $\alpha$-stable matching $\mu$. An *improvement* of $\mu$ is an $\alpha$-stable matching $N$ with at least one change in which every changed student strictly improves and every changed school strictly worsens. Then the student rank vector of $\mu$ is optimal among $\alpha$-stable matchings if and only if $\mu$ has no improvement.
--
--   Both readings of *optimal* are stated: coordinatewise ($\mathrm{rk}_d(\mu(d))\le\mathrm{rk}_d(\nu(d))$ for every $\alpha$-stable $\nu$ and every student $d$), and lexicographic in every public student order $\rho$ (no $\alpha$-stable $\nu$ has a lexicographically smaller rank vector). The lemma lets Theorem D.8's certificate prove rank optimality without exhibiting an optimal matching.
--
--   Differences from the source:
--   - reading: the student rank vector of µ is optimal among α-stable matchings → two conjuncts: coordinatewise optimality ↔ no improvement, and for every public order ρ, lexicographic optimality ↔ no improvement; reason: the word admits both readings (they agree because a student-best α-stable matching exists, Lemma D.9); both are stated
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 102, Lemma D.19

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- Lemma D.19 (p. 102): for strong or super stability, the student rank vector of an
`α`-stable `µ` is optimal among `α`-stable matchings if and only if `µ` has no improvement.
Optimality is stated both coordinatewise and lexicographically in every public student order. -/
theorem lemma_D_19 {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (hP : ∀ i, IsRow (P i)) (hQ : ∀ h, IsRow (Q h)) (α : StabKind) (hα : α ≠ StabKind.weak)
    (μ : Matching n m) (hμ : IsStable α P Q μ) :
    ((∀ ν : Matching n m, IsStable α P Q ν → ∀ d, rk (P d) (μ.toFun d) ≤ rk (P d) (ν.toFun d)) ↔
        ¬ ∃ N : Matching n m, IsImprovement α P Q μ N) ∧
      ∀ ρ : Fin n ≃ Fin n,
        ((∀ ν : Matching n m, IsStable α P Q ν → ¬ List.Lex (· < ·) (rankVec ρ P ν) (rankVec ρ P μ)) ↔
          ¬ ∃ N : Matching n m, IsImprovement α P Q μ N) := by sorry

end MatchIndiff.PublicSM
