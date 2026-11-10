-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_theorem_4_24
-- name    : MultAddExt.Multiplicative.theorem_4_24
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:39.747257+00:00
-- url     : https://prove2.me/theorems/c2e7a44e-bd36-40ef-9be3-a337f0196d3c
-- title:
--   Theorem 4.24 — Li's extractor for one source and one block-wise source, error 2^{-r^{1/c_IExt}} ([Li15, Theorem 1.4])
-- statement:
--   There is a universal constant $c_{\mathrm{IExt}}>1$ such that for every sufficiently large $n$ and every real $r$ with $\log^{12}n\le r\le n$ there is an explicit polynomial-time function
--   $$\mathrm{IExt}_0:\{0,1\}^n\times\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^{\lfloor 0.9r\rfloor}$$
--   such that whenever $U$ is independent of $(A,B)$, $H_\infty(U)\ge r$, and $(A,B)$ is an $(r,r)$-block-wise source,
--   $$\mathrm{SD}\bigl(\mathrm{IExt}_0(U,A,B),\,U_{\lfloor 0.9r\rfloor}\bigr)\le 2^{-r^{1/c_{\mathrm{IExt}}}}.$$
--   Explicit: one polynomial-time machine computes $\mathrm{IExt}_0(u,a,b)$ from $(\lfloor r\rfloor,\lfloor0.9r\rfloor,u,a,b)$.
--
--   This cited extractor is the final component of the multiplicative extractor of Theorem 4.41; its constant $c_{\mathrm{IExt}}$ enters the output exponent $\alpha'=\alpha\delta_{\mathrm{out}}^2/(8c_{\mathrm{IExt}})$.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: explicit polynomial-time computable function → PolyTimeComputable f: Mathlib Turing.TM2ComputableInPolyTime over the alphabet Bool, and the family is the restriction of f to the relevant input lengths; reason: Mathlib's multi-stack Turing machine is polynomially equivalent to the multi-tape model
--   - reading: an explicit polynomial-time function, for each admissible choice of the parameters → one polynomial-time machine f that receives (⌊r⌋, ⌊0.9r⌋, u‖a‖b) through pairEnc/unary and outputs the function value; reason: one uniform algorithm on the rounded entropy and the requested output length; supplying the latter avoids identifying two instances with different output lengths but the same integer part of r
--   - reading: 0.9r output bits → ⌊0.9r⌋ output bits; reason: an output length is an integer and r is real
--   - reading: 2^{−r^{Ω(1)}}-close to uniform; in particular a universal c_IExt > 1 with error at most 2^{−r^{1/c_IExt}} for all sufficiently large admissible parameters → ∃ c_IExt > 1 (universal, before the machine and n₀) with statDist ≤ 2^{−r^{1/c_IExt}} for all n ≥ n₀ and admissible r; reason: the paper's own "in particular" form, equivalent to the Ω(1) form; admissible r ≥ log¹² n is large once n is
--   - encoding: U independent of (A, B) → the product distribution prodDist U AB; reason: independence means the joint law is the product
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 22 (PDF 26), Theorem 4.24

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_Hardness

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Theorem 4.24** (One independent source and one block-wise source [Li15, Theorem 1.4]), p. 22,
in its "in particular" form. There is a universal `c_IExt > 1` such that for every sufficiently large
`n` and every `r` with `log¹² n ≤ r ≤ n` there is an explicit polynomial-time function
`IExt₀ : {0,1}ⁿ × {0,1}ⁿ × {0,1}ⁿ → {0,1}^{⌊0.9r⌋}` such that, whenever `U` is independent of
`(A, B)`, `H∞(U) ≥ r` and `(A, B)` is an `(r, r)`-block-wise source, `IExt₀(U, A, B)` is
`2^{−r^{1/c_IExt}}`-close to uniform. One machine `f` computes `IExt₀` from `(⌊r⌋, ⌊0.9r⌋, u, a, b)`. -/
theorem theorem_4_24 : ∃ cIExt : ℝ, 1 < cIExt ∧
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ r : ℝ, Real.logb 2 n ^ 12 ≤ r → r ≤ n →
    ∃ IExt : (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → (Fin ⌊(0.9 : ℝ) * r⌋₊ → Bool),
      (∀ u a b, f (pairEnc (unary ⌊r⌋₊) (pairEnc (unary ⌊(0.9 : ℝ) * r⌋₊)
          (List.ofFn u ++ List.ofFn a ++ List.ofFn b))) =
        List.ofFn (IExt u a b)) ∧
      ∀ (U : (Fin n → Bool) → ℝ) (AB : (Fin n → Bool) × (Fin n → Bool) → ℝ),
        IsDist U → IsDist AB → r ≤ minEntropy U → IsBlockwiseSource AB r r →
        statDist (pushforward (fun z => IExt z.1 z.2.1 z.2.2) (prodDist U AB))
            (uniform (Fin ⌊(0.9 : ℝ) * r⌋₊ → Bool)) ≤ (2 : ℝ) ^ (-(r ^ (1 / cIExt))) := by sorry

end MultAddExt.Multiplicative
