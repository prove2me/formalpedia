-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_15
-- name    : MatchIndiff.PublicSM.lemma_D_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:41.253859+00:00
-- url     : https://prove2.me/theorems/56cba4e7-99cc-4b33-98f7-11807b27e294
-- title:
--   Lemma D.15 — equal-rank strongly stable matchings are the perfect matchings of the tie graph
-- statement:
--   Let $\mu$ be strongly stable. Its *tie graph* has the matched students on one side and the matched schools on the other, with an edge $(d,h)$ exactly when $h\sim_d\mu(d)$ and $d\sim_h\mu(h)$. Then a matching $\nu$ is strongly stable with the same student rank vector as $\mu$ if and only if $\nu$ is a perfect matching of the tie graph of $\mu$ with all remaining participants unmatched:
--   $$\nu\ \text{strongly stable},\ \mathrm{rk}(\nu)=\mathrm{rk}(\mu)\iff \nu\subseteq\text{tie graph},\ \text{and }\nu,\mu\text{ match the same students and schools}.$$
--
--   Differences from the source:
--   - encoding: students N, schools H, weak rows, ⊥ with rank m + 1 → Fin n, Fin m, rows r : Fin k → ℕ with IsRow (0 = unacceptable, j = j-th tie class), rk with ⊥ ↦ k + 1 and unacceptable ↦ k + 2, matchings with Option values; reason: Lean convention; the gap-free row encoding is a bijection with the paper's rows and rk orders partners exactly as the paper does
--   - encoding: perfect matching of the tie graph, all remaining participants unmatched → every pair of ν is a tie-graph edge, and ν, μ have the same matched students and the same matched schools; reason: Lean convention; the same condition
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 97, Lemma D.15

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model

namespace MatchIndiff.PublicSM

/-- Lemma D.15 (p. 97): the strongly stable matchings with the same student rank vector as a
strongly stable `µ` are exactly the perfect matchings of the tie graph of `µ`, with all remaining
participants unmatched. -/
theorem lemma_D_15 {n m : ℕ} (P : Fin n → Fin m → ℕ) (Q : Fin m → Fin n → ℕ)
    (hP : ∀ i, IsRow (P i)) (hQ : ∀ h, IsRow (Q h)) (μ : Matching n m)
    (hμ : IsStable StabKind.strong P Q μ) (ν : Matching n m) :
    (IsStable StabKind.strong P Q ν ∧ ∀ i, rk (P i) (ν.toFun i) = rk (P i) (μ.toFun i)) ↔
      ((∀ d h, ν.toFun d = some h → TieEdge P Q μ d h) ∧
        (∀ d, (ν.toFun d).isSome = (μ.toFun d).isSome) ∧
        ∀ h, (ν.holder h).isSome = (μ.holder h).isSome) := by sorry

end MatchIndiff.PublicSM
