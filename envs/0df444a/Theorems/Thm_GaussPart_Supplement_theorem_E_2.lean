-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_E_2
-- name    : GaussPart.Supplement.theorem_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:14:36.72017+00:00
-- url     : https://prove2.me/theorems/6260f310-848e-4e42-912b-63e6f7ad4228
-- title:
--   Theorem E.2 — multiplicative-approximation SQ lower bound $d^{-\Omega(\deg_{1,4c}(f))}$ (corrected: $\deg_{1,4c}(f)\ge1$)
-- statement:
--   **Setting.** Fix $a\in(0,1/2)$; $b>0$ is a sufficiently small constant depending on $a$. Let $c\in(0,1/4)$, $\epsilon\in(0,c]$, and assume $2c\ge d^{-b}$. Let $K\le d^a$, fix a Boolean $f:\mathbb R^K\to\{\pm1\}$, and let $\mathcal F$ be a class of functions on $\mathbb R^d$ containing every orthogonal embedding $x\mapsto f(Px)$, $PP^\top=I_K$. Set $r:=\deg_{1,4c}(f)$, the least degree of a polynomial within $L_1(\mathcal N(0,I_K))$-distance less than $4c$ of $f$, and assume $r\ge1$.
--
--   **Theorem.** Any SQ algorithm that agnostically learns $\mathcal F$ under $\mathcal N(0,I_d)$ to error $(1+c)\mathrm{opt}+\epsilon$ either makes a query of tolerance at most
--   $$
--   d^{-\Omega(r)}
--   $$
--   or makes at least $2^{d^{\Omega(1)}}$ queries.
--
--   This shows that the dimension exponent of Theorem 4.2, governed by a Gaussian approximation degree at accuracy $O(c)$, cannot be improved in the SQ model beyond polynomial factors.
--
--   **Formalization Note** $b$ and the two $\Omega$-constants may depend on $a$; "agnostically learns" is: for every labeled distribution with x-marginal $\mathcal N(0,I_d)$ and arbitrary labels, against every valid oracle, success probability at least $2/3$.
--
--   Differences from the source:
--   - correction: r := deg_{1,4c}(f), any value → r ≥ 1 assumed; reason: for r = 0 the statement is false: f ≡ 1 and F = {1}; the algorithm that asks nothing and outputs the constant 1 learns to error opt, but makes no query of tolerance at most d⁰ = 1 and fewer than 2^{d^{c₁}} queries
--   - reading: agnostically learns F to error (1 + c)opt + ϵ (no confidence stated) → with probability at least 2/3; reason: the confidence of Definition 1.4
--   - reading: f : ℝ^K → {±1} → a Borel measurable ±1-valued function; reason: Boolean functions are Borel measurable (Definition A.1)
--   - encoding: any SQ algorithm (Definition A.4) that makes no query of tolerance at most τ₀ → every randomized adaptive SQ algorithm of the published SQAlg type whose every query is a measurable [−1,1]-valued function with tolerance > τ₀, against adversarial trajectory-dependent oracles; reason: the published SQ model; states no run reaches can be changed without changing any run
--   - reading: requires 2^{d^{Ω(1)}} queries → on some admissible instance, against some valid oracle, some run makes at least 2^{d^{c₁}} queries with positive probability; reason: worst-case query complexity of a randomized SQ algorithm
--   - encoding: b sufficiently small; Ω(·) with a fixed → ∀ a ∃ b > 0 ∃ c₁ c₂ > 0 chosen before c, ϵ, d, K, f, F; reason: the constants may depend on the fixed a
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem E.2, p.78 (PDF p.80); deg_{1,ϵ}, p.77 (PDF p.79)

import Mathlib
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_L1Degree
import Definitions.Def_GaussPart_Supplement_SQ

open MeasureTheory ProbabilityTheory Matrix PrivLearn.SQSim

namespace GaussPart

namespace Supplement

/-- **Theorem E.2** (Multiplicative Approximation SQ Lower Bound), with the degenerate case
`deg_{1,4c}(f) = 0` excluded.

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem E.2, p.78 (PDF p.80);
`deg_{1,ϵ}` defined on p.77 (PDF p.79).

"Fix a constant a ∈ (0, 1/2). There is a sufficiently small constant b > 0 for which the following
holds. Fix c ∈ (0, 1/4) and ϵ ∈ (0, c], and assume 2c ≥ d^{−b}. Let K ≤ d^a, fix f : ℝ^K → {±1}, and
let F ⊆ {ℝ^d → {±1}} such that {f(Px) : P ∈ ℝ^{K×d}, PP^⊤ = I_K} ⊆ F. Set r := deg_{1,4c}(f). Then any
SQ algorithm that agnostically learns F under N(0, I_d) to error (1 + c)opt + ϵ either makes a query
of tolerance at most d^{−Ω(r)} or makes at least 2^{d^{Ω(1)}} queries."

**Formalization Note.**
* **Correction.** The hypothesis `r ≥ 1` is added. For `r = 0` the statement is false: take `f ≡ 1`
  (so `r = 0`) and `F = {1}`; the algorithm that asks nothing and outputs the constant `1` has error
  `opt ≤ (1 + c)opt + ϵ`, yet makes no query of tolerance at most `d⁰ = 1` and fewer than `2^{d^{c₁}}`
  queries.
* `b` and the constants `c₁, c₂` of the two `Ω(·)` may depend on `a`; they are chosen before
  `c, ϵ, d, K, f, F`. `f` is Borel measurable (`IsBoolFn`), the paper's convention for Boolean
  functions; `r = l1Degree f (4c)` with the strict inequality of the definition.
* "Agnostically learns `F` under `N(0, I_d)`" is: for every distribution `D` on `ℝᵈ × {±1}` with
  x-marginal `N(0, I_d)` and arbitrary labels, against every valid oracle for `D`, the output law
  gives mass `≥ 2/3` (the confidence of Definition 1.4) to hypotheses `h` with
  `err_D(h) ≤ (1 + c)opt_D(F) + ϵ`. SQ algorithms, tolerances and query counts are as in
  `theorem_5_4`. -/
theorem theorem_E_2 :
    ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ b : ℝ, 0 < b ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (c ε : ℝ), 0 < c → c < 1 / 4 → 0 < ε → ε ≤ c →
    ∀ d : ℕ, (d : ℝ) ^ (-b) ≤ 2 * c →
    ∀ K : ℕ, (K : ℝ) ≤ (d : ℝ) ^ a →
    ∀ f : Vec K → ℝ, IsBoolFn f → 1 ≤ l1Degree f (4 * c) →
    ∀ F : Set (Vec d → ℝ),
      (∀ U : Matrix (Fin K) (Fin d) ℝ, U * Uᵀ = 1 → (fun x => f (matVec U x)) ∈ F) →
    ∀ (St : Type) (B : SQAlg (Vec d × ℝ) (Vec d → ℝ) St),
      TolAbove B ((d : ℝ) ^ (-(c₂ * l1Degree f (4 * c)))) →
      (∀ D : Measure (Vec d × ℝ), IsLabeledLaw D → D.map Prod.fst = stdGaussian (Vec d) →
        ∀ O : List St → ℝ, B.IsValidOracle D O →
          (2 / 3 : ENNReal) ≤ successMass B O
            {h | err D h ≤ ENNReal.ofReal (1 + c) * opt D F + ENNReal.ofReal ε}) →
      ∃ D : Measure (Vec d × ℝ), IsLabeledLaw D ∧ D.map Prod.fst = stdGaussian (Vec d) ∧
        ∃ O : List St → ℝ, B.IsValidOracle D O ∧
          MakesManyQueries B O ((2 : ℝ) ^ ((d : ℝ) ^ c₁)) := by sorry

end Supplement

end GaussPart
