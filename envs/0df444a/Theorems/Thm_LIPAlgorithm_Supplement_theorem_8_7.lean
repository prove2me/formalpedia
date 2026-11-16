-- Prove2me | Theorems.Thm_LIPAlgorithm_Supplement_theorem_8_7
-- name    : LIPAlgorithm.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:55:25.608007+00:00
-- url     : https://prove2.me/theorems/abc3e767-3c63-4abc-9341-380abdd76bfe
-- title:
--   Theorem 8.7 — BHT speedup, well-rounded case: one isomorphism or $\emptyset$ in quantum time $O(n^2\log n)^{n/3}2^{\mathrm{polylog}(\kappa)}$ with QRAM of size $O(n^2\log n)^{n/3}$
-- statement:
--   Let $n\ge1$ and let $G_1,G_2\in\mathbb Z^{n\times n}$ be integral, positive definite and well-rounded Gram matrices (rank-$n$ well-rounded integral lattices), of encoding length $\ell$. In the QRAM model there are one hybrid quantum–classical machine $M$ and constants $C,K,\kappa_0\in\mathbb N$, $c>0$, all fixed before the input, such that for every $\kappa\ge\kappa_0\,n\log n$ the following holds for the run of $M$ on input $\kappa$ (in unary) followed by $G_1,G_2$.
--
--   1. Every branch of positive probability halts with cost at most
--   $$\Big\lceil \big(C n^2\log(n+2)\big)^{n/3}\,2^{(\log_2(\kappa+2))^K}\,(\kappa+\ell+1)^K\Big\rceil$$
--   and QRAM size at most $\lceil (C n^2\log(n+2))^{n/3}\rceil$ cells.
--   2. With probability at least
--   $$1-\exp(-c\,\kappa)$$
--   the machine decides whether $G_1,G_2$ are isomorphic: if $\mathrm{Iso}(G_1,G_2)\ne\emptyset$ it outputs a single isomorphism $U\in\mathrm{Iso}(G_1,G_2)$, and otherwise it outputs $\emptyset$.
--
--   This is the quantum (Brassard–Høyer–Tapp) speedup of the birthday search of the classical algorithm: in the well-rounded case one isomorphism is found in time $O(n^2\log n)^{n/3}$, the cube root of the collision scale, instead of the classical $O(n\sqrt{\log n})^n$.
--
--   **Formalization Note** The QRAM model is the definition `qProb` of this mission. The bounds are worst case over all measurement outcomes. The confidence parameter $\kappa$ is given in unary, as in the published Theorem 7.1. The outputs are the lists $[U]$ and $[\,]$ in the published encoding `encMatList`.
--
--   Differences from the source:
--   - reading: In the QRAM model, there is a quantum algorithm → one hybrid machine M of qProb (a TM2 controller fixed before the input, quantum calls over {H, T, CNOT} and unit-cost QRAM gates), with C, K, κ₀, c chosen before the instance; reason: §8.1 fixes the standard circuit model with cost = gates + oracle calls + QRAM calls; the oracles are circuits (Lemma 8.5, Fact 8.2); the classical control is the base mission's TM2
--   - encoding: time O(n² log n)^{n/3} 2^{polylog(κ)} → cost at most budgetQWR C K n κ ℓ = ⌈(C·n²·log(n+2))^{n/3}·2^{(log₂(κ+2))^K}·(κ+ℓ+1)^K⌉; reason: footnote 2 (O(f(n))ⁿ = (C f(n))ⁿ), Remark 2.2 (all running times suppress poly(n, bits)); log(n+2) replaces log n, which is 0 at n = 1
--   - encoding: QRAM of size O(n² log n)^{n/3} → at most qramBound C n = ⌈(C·n²·log(n+2))^{n/3}⌉ cells, no polynomial factor; reason: footnote 2; the theorem states the size without a polynomial factor
--   - reading: running time of a quantum algorithm → worst case: qProb … (fun _ => True) = 1, i.e. every branch of positive probability halts within the cost and QRAM bounds; reason: the proof truncates the BHT schedule (Lemma 8.4(ii)), so a worst-case bound is what it provides; this is the stronger reading
--   - encoding: rank-n well-rounded integral lattices L1, L2 → n ≥ 1 and Gram matrices G₁, G₂ that are integral, positive definite and well-rounded (published IsGram, IsWellRoundedGram); reason: §2.2, pp.10–11; rank 0 is the degenerate empty case
--   - encoding: κ = Ω(n log n) → κ ∈ ℕ written in unary before the instance, for every κ ≥ κ₀·n·log n with κ₀ chosen before the instance; reason: the machine must receive κ, and the budget contains the factor (κ+ℓ+1)^K, so reading κ in unary costs nothing; the published theorem_7_1 reads κ the same way
--   - encoding: probability 1 − exp(−Ω(κ)) → probability at least 1 − exp(−c·κ) with c > 0 chosen before the instance; reason: the Ω constant is universal
--   - encoding: decides whether L1, L2 are isomorphic and, if so, outputs a single isomorphism O ∈ Iso(L1, L2); otherwise it outputs ∅ → output encMatList [U] with U ∈ isoSet G₁ G₂, or encMatList [] when isoSet G₁ G₂ = ∅; reason: the published output encoding; the two outputs differ, so the decision is read off the output
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 8.7, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_LIPAlgorithm_Gram
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_Supplement_qProb
import Definitions.Def_LIPAlgorithm_Supplement_budgetQ

namespace LIPAlgorithm

namespace Supplement

/-- **Theorem 8.7 (BHT speedup, well-rounded case).** Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time
Algorithm for the Lattice Isomorphism Problem*, STOC 2027 submission (manuscript sha256 61ee52aa…),
Theorem 8.7, p.45 (PDF p.48).

One hybrid QRAM machine and constants `C`, `K`, `κ₀`, `c > 0`, before the instance: for `n ≥ 1`,
integral well-rounded `G₁`, `G₂` and `κ ≥ κ₀·n·log n`, on input `κ` (unary) followed by the instance,
every branch of positive probability halts within cost
`⌈(C·n²·log(n+2))^{n/3}·2^{(log₂(κ+2))^K}·(κ+ℓ+1)^K⌉` and QRAM size `⌈(C·n²·log(n+2))^{n/3}⌉` cells,
and with probability at least `1 − exp(−c·κ)` the output is the one-element list `[U]` of some
`U ∈ Iso(G₁, G₂)`, or the empty list ("∅") when `Iso(G₁, G₂)` is empty.

**Formalization Note.** The QRAM model is `qProb` (§8.1, Definition 8.3): a TM2 controller with
quantum calls over `{H, T, CNOT}` and unit-cost QRAM gates, cost = controller steps + gates. The time
and QRAM bounds are worst case (`qProb … (fun _ => True) = 1`). `κ` is read in unary before the instance,
as in the published `theorem_7_1`; `log(n+2)` replaces `log n` in the budgets; the exponent `n/3` is
real. The output encoding is the published `encMatList`. -/
theorem theorem_8_7 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K κ₀ : ℕ) (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G₁ G₂ : Gram n) (κ : ℕ), 1 ≤ n → IsGram G₁ → IsGram G₂ →
        IsWellRoundedGram G₁ → IsWellRoundedGram G₂ →
        (κ₀ : ℝ) * n * Real.log n ≤ κ →
        let inp := List.replicate κ true ++ [false] ++ encInst G₁ G₂
        let B := budgetQWR C K n κ (encInst G₁ G₂).length
        let S := qramBound C n
        qProb M inp B S (fun _ => True) = 1 ∧
        1 - Real.exp (-(c * κ)) ≤
          qProb M inp B S fun out =>
            (isoSet G₁ G₂ = ∅ ∧ out = encMatList ([] : List (Gram n))) ∨
              ∃ U ∈ isoSet G₁ G₂, out = encMatList [U] := by sorry

end Supplement

end LIPAlgorithm
