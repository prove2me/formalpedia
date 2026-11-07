-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_A_3
-- name    : MatMulTimeLP.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:00.485134+00:00
-- url     : https://prove2.me/theorems/24d87685-b18c-487f-90b7-bd883be4230e
-- title:
--   Lemma A.3 — Sample returns $i$ with probability exactly $r_i^2/U$
-- statement:
--   Let $n=2^D$, $D\ge 1$, $n\ge k$. Fix $G$, and suppose the current residual $r$ is accurate for $G$ and $U\ge 4E$, with $E=\|r\|_2^2$. Then Sample$(U)$ returns coordinate $i$ with probability exactly $r_i^2/U$, and $\bot$ with the remaining probability $1-E/U$. In particular, the distribution of the answer does not depend on $G$.
--
--   So at an accurate residual the answer reveals nothing about the sketch, which is what makes the data structure safe against an adaptive caller.
--
--   **Formalization Note** The conclusion is stated for every test function $\varphi$ of the answer: $\mathbb E[\varphi]=\sum_i\frac{r_i^2}{U}\varphi(i)+(1-\frac EU)\varphi(\bot)$. Indicators give each probability, and also probability $0$ of Fail.
--
--   Differences from the source:
--   - encoding: the probabilities of the answers of Sample($U$) → the expectation identity of the finite tree `sampleExp`, for every test function; reason: equivalent to the probabilities of all answers
--   - encoding: $U\ge 4E$, including $U=0$ → at $U=0$ (so $E=0$), Lean's $0/0=0$ gives $\bot$ with probability $1$; reason: this agrees with the proof on p.47, "If $E=0$ … returns $\bot$"
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma A.3, p.46

import Mathlib
import Definitions.Def_MatMulTimeLP_Sampler

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma A.3, p.46: for fixed `G`, if `r` is accurate for `G` and
`U ≥ 4E`, then `Sample(U)` returns `i` with probability exactly `rᵢ²/U`, and `⊥` with the remaining probability
`1 - E/U`; so the law of the answer does not depend on `G`.

**Formalization Note** The conclusion is for every test function `φ` of the answer, which gives each probability
(take an indicator), probability `0` of `Fail`, and independence of `G` at once. At `U = 0`, where `E = 0`, Lean's
`0/0 = 0` gives `⊥` with probability `1`, as the proof on p.47 says. -/
theorem lemma_A_3 (D : ℕ) (hD : 1 ≤ D) (hk : skK D ≤ 2 ^ D)
    (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ) (U : ℝ) (hacc : Accurate D G r)
    (hU : 4 * energyE r ≤ U) (φ : Answer (2 ^ D) → ℝ) :
    sampleExp D G r U φ =
      ∑ i, r i ^ 2 / U * φ (Answer.coord i) + (1 - energyE r / U) * φ Answer.bot := by sorry

end MatMulTimeLP
