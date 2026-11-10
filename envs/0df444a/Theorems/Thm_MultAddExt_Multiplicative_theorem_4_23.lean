-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_theorem_4_23
-- name    : MultAddExt.Multiplicative.theorem_4_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:40.597195+00:00
-- url     : https://prove2.me/theorems/63c95107-5e3c-4255-a854-be93ca100713
-- title:
--   Theorem 4.23 — explicit errorless two-source condenser with output min-entropy 3m/4 ([BCDT19, Theorem 27])
-- statement:
--   There is a universal constant $C_{2\mathrm{Cond}}\ge 1$ such that for every sufficiently large $n$ and all real $r$ and integers $m$ with
--   $$\log n\le m,\qquad (m\log n)^{C_{2\mathrm{Cond}}}\le r\le n,$$
--   there is an explicit polynomial-time function $2\mathrm{Cond}_0:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ such that for every pair of independent sources $U,V$ on $\{0,1\}^n$ with $H_\infty(U),H_\infty(V)\ge r$,
--   $$H_\infty\bigl(2\mathrm{Cond}_0(U,V)\bigr)\ge 3m/4.$$
--   Explicit: a single polynomial-time machine computes $2\mathrm{Cond}_0(u,v)$ from $(\lfloor r\rfloor, m, u, v)$.
--
--   This cited result (a consequence of Ben-Aroya, Cohen, Doron and Ta-Shma) is the two-source component of the robust block condenser of Theorem 4.43.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: explicit polynomial-time computable function → PolyTimeComputable f: Mathlib Turing.TM2ComputableInPolyTime over the alphabet Bool, and the family is the restriction of f to the relevant input lengths; reason: Mathlib's multi-stack Turing machine is polynomially equivalent to the multi-tape model
--   - reading: an explicit polynomial-time function, for each admissible choice of the parameters → one polynomial-time machine f that receives (⌊r⌋, m, u‖v) through pairEnc/unary and outputs the function value; reason: explicitness is read as one algorithm on discrete construction parameters; entropy thresholds remain real in the guarantee, and their integer parts index the construction; all relevant lengths are supplied separately
--   - encoding: independent sources U, V → the product distribution prodDist U V; reason: independence of a pair means its law is the product
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), pp. 21–22 (PDF 25–26), Theorem 4.23

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_Hardness

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Theorem 4.23** (Errorless two-source condensation [BCDT19, Theorem 27]), pp. 21–22. There is a
universal constant `C_2Cond ≥ 1` such that, for every sufficiently large `n` and all `r, m` with
`log n ≤ m` and `(m log n)^{C_2Cond} ≤ r ≤ n`, there is an explicit polynomial-time function
`2Cond₀ : {0,1}ⁿ × {0,1}ⁿ → {0,1}^m` with `H∞(2Cond₀(U, V)) ≥ 3m/4` for all independent `U, V`
on `{0,1}ⁿ` with `H∞(U), H∞(V) ≥ r`. One machine `f` computes `2Cond₀` from `(⌊r⌋, m, u, v)`. -/
theorem theorem_4_23 : ∃ C2Cond : ℝ, 1 ≤ C2Cond ∧
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (r : ℝ) (m : ℕ), Real.logb 2 n ≤ m → ((m : ℝ) * Real.logb 2 n) ^ C2Cond ≤ r → r ≤ n →
    ∃ Cond : (Fin n → Bool) → (Fin n → Bool) → (Fin m → Bool),
      (∀ u v, f (pairEnc (unary ⌊r⌋₊) (pairEnc (unary m) (List.ofFn u ++ List.ofFn v))) =
        List.ofFn (Cond u v)) ∧
      ∀ U V : (Fin n → Bool) → ℝ, IsDist U → IsDist V → r ≤ minEntropy U → r ≤ minEntropy V →
        3 * (m : ℝ) / 4 ≤ minEntropy (pushforward (fun z => Cond z.1 z.2) (prodDist U V)) := by sorry

end MultAddExt.Multiplicative
