-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_A_4
-- name    : MatMulTimeLP.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:29.505208+00:00
-- url     : https://prove2.me/theorems/fcba5a71-dcf8-4453-9908-cfdafaa2bde2
-- title:
--   Lemma A.4 — coupling with the independent sampler against an adaptive adversary
-- statement:
--   Let $n=2^D$, $D\ge 1$, $n\ge k$. Consider any adaptive adversary issuing at most $n^3$ operations, where each query satisfies $U\ge 4\|r\|_2^2$, and where each operation may depend on all previous answers. Then the data structure and the independent sampler can be coupled such that, with probability at least $1-n^{-10}$, they return the same answer to every query.
--
--   This removes the dependence between the sketch and the residuals the caller queries: the algorithm can be analysed as though it used the ideal sampler.
--
--   **Formalization Note** The coupling is a probability law on pairs of transcripts, whose first marginal is the data structure's law (the mixture over $G$) and whose second marginal is the independent sampler's law. The adversary sees neither $G$ nor any internal draw, by its type.
--
--   Differences from the source:
--   - generalization: each query satisfies $U\ge 4\|r\|_2^2$ → required only along answer sequences without Fail; reason: the independent sampler never answers Fail, so the proof needs no more; an adversary meeting the condition everywhere is an instance
--   - encoding: an adversary issuing at most $n^3$ operations → any adversary, with runs stopped after $n^3$ operations; reason: an adversary issuing at most $n^3$ is unaffected by the stop
--   - encoding: "can be coupled" → `∃ c : PMF (Transcript × Transcript)` with the two marginals and $c\{p_1\ne p_2\}\le n^{-10}$; reason: the literal meaning of a coupling; transcripts form a countable set
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma A.4, p.47; the adversary, p.32

import Mathlib
import Definitions.Def_MatMulTimeLP_Sampler

namespace MatMulTimeLP

open MeasureTheory

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma A.4, p.47: against any adaptive adversary issuing at most
`n³` operations, where each query satisfies `U ≥ 4‖r‖₂²`, the data structure and the independent sampler can be
coupled so that they return the same answer to every query with probability at least `1 - n⁻¹⁰`.

**Formalization Note** "Coupled" is literal: a probability law `c` on pairs of transcripts whose first marginal is
the data structure's (the `G`-mixture of `dsProb`) and whose second is the independent sampler's, with
`c{p | p.1 ≠ p.2} ≤ n⁻¹⁰`. Runs stop after `n³` operations, so "at most `n³`" holds for every adversary, and
one issuing fewer is unaffected. The condition on queries is needed only along answer sequences without `Fail`,
which is weaker than requiring it everywhere. `n = 2^D`, `n ≥ k`, `D ≥ 1`, `z` starts at `0`. -/
theorem lemma_A_4 (D : ℕ) (hD : 1 ≤ D) (hk : skK D ≤ 2 ^ D)
    (H : Matrix (Fin (2 ^ D)) (Fin (2 ^ D)) ℝ) (h : Fin (2 ^ D) → ℝ) (adv : Adversary (2 ^ D))
    (hadv : ValidAdv H h adv ((2 ^ D) ^ 3) 0 []) :
    ∃ c : PMF (Transcript (2 ^ D) × Transcript (2 ^ D)),
      (∀ t, (c.map Prod.fst) t =
        ∫⁻ G, ENNReal.ofReal (dsProb D G H h adv ((2 ^ D) ^ 3) 0 [] t) ∂sketchLaw (skK D) (2 ^ D)) ∧
      (∀ t, (c.map Prod.snd) t = ENNReal.ofReal (idealProb H h adv ((2 ^ D) ^ 3) 0 [] t)) ∧
      c.toOuterMeasure {p | p.1 ≠ p.2} ≤ ENNReal.ofReal (1 / ((2 : ℝ) ^ D) ^ 10) := by sorry

end MatMulTimeLP
