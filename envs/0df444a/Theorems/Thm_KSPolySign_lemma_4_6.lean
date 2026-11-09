-- Prove2me | Theorems.Thm_KSPolySign_lemma_4_6
-- name    : KSPolySign.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:19.130302+00:00
-- url     : https://prove2.me/theorems/392fac3d-ec89-48fc-b7ae-647f96440178
-- title:
--   Lemma 4.6 — partial signing by grouped coordinates
-- statement:
--   Let $b_1,\dots,b_m\in\mathbb R^{d}$ have rational entries and Euclidean norm at most two, and let $0<\eta<1$. A deterministic algorithm returns $y\in[-1,1]^m$ such that
--
--   1. at most $d$ coordinates are fractional: $|\{i:|y_i|<1\}|\le d$;
--   2. $\big\|\sum_iy_ib_i\big\|_2\le\eta$;
--   3. it uses $\tilde O(md+d^4)$ arithmetic operations, the suppressed factors including $\log(1/\eta)$.
--
--   This partial signing reduces the number of fractional coordinates of the matrix inputs to at most $n^2$ before the potential descent starts.
--
--   **Formalization Note** One deterministic program of the published real RAM, restricted to rational literals and no square roots or random draws (`VecBalPoly.Admissible`); arithmetic operations are additions, subtractions, multiplications, divisions and comparisons of reals (`VecBalPoly.realOps`). $\tilde O(md+d^4)$ is $C(md+d^4)\big(\log(m+d+2)+\log(1/\eta)\big)^k$ with $C,k$ fixed before the input.
--
--   Differences from the source:
--   - reading: a deterministic algorithm with Õ(md + d⁴) arithmetic operations → one VecBalPoly.Admissible program on the published real RAM whose realOps count is ≤ C(md + d⁴)(log(m + d + 2) + log(1/η))^k, C, k fixed before the input; reason: the paper counts +, −, ×, ÷ and comparisons on reals (proof p.40); Õ suppresses logarithmic factors in m, d and 1/η
--   - reading: d_vec arbitrary → d ≥ 1; reason: at d = 0 the printed bound is 0, while writing m output coordinates requires reading m with comparisons; the bound is meant for d ≥ 1
--   - encoding: input b_1, …, b_m and η; output y → input vecLayout m d b η; y = the m cells after the input when the run halts; every tape ω; reason: an admissible program makes no random draws, so the tape is irrelevant
--   - encoding: norm at most two → ∑_j b_ij² ≤ 4; reason: same condition
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.6, p.39 (PDF p.39)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_vecLayout
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 4.6 (Partial signing by grouped coordinates).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.6, p.39 (PDF p.39).

Let `b_1, …, b_m ∈ ℝ^{d}` have rational entries and norm at most two, and let `0 < η < 1`. A
deterministic algorithm returns `y ∈ [−1, 1]^m` with at most `d` fractional coordinates and
`‖∑ y_ib_i‖₂ ≤ η`, using `Õ(md + d⁴)` arithmetic operations, the suppressed factors including
`log(1/η)`.

**Formalization Note** One `VecBalPoly.Admissible` program (rational literals, no square root, no
random draws: deterministic exact real arithmetic) on the published real RAM; arithmetic
operations are `VecBalPoly.realOps` (`+, −, ×, ÷`, comparisons). The input is `vecLayout m d b η`; `y` is
the `m` cells after the input when the run halts. `Õ(md + d⁴)` is `C(md + d⁴)(log(m + d + 2) + log(1/η))^k`
with `C, k` fixed before the input. `d ≥ 1`; `η` is an input of the algorithm (any real in `(0, 1)`). The tape
`ω` is irrelevant for an admissible program. -/
theorem lemma_4_6 :
    ∃ P : MatMulTimeLP.Program, VecBalPoly.Admissible P ∧ ∃ C k : ℕ,
      ∀ (m d : ℕ), 1 ≤ d → ∀ (b : Fin m → Fin d → ℝ) (η : ℝ),
        (∀ i j, ∃ q : ℚ, b i j = q) → (∀ i, ∑ j, b i j ^ 2 ≤ 4) → 0 < η → η < 1 →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (vecLayout m d b η) ω t ∧
          (VecBalPoly.realOps P (vecLayout m d b η) ω t : ℝ) ≤
            C * ((m : ℝ) * d + (d : ℝ) ^ 4) * (Real.log (m + d + 2) + Real.log (1 / η)) ^ k ∧
          (let y := MatMulTimeLP.outputAt P (vecLayout m d b η) ω t m
           (∀ i, |y i| ≤ 1) ∧ (Finset.univ.filter (fun i => |y i| < 1)).card ≤ d ∧
             Real.sqrt (∑ j, (∑ i, y i * b i j) ^ 2) ≤ η) := by sorry

end KSPolySign
