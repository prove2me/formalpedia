-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_theorem_4_43
-- name    : MultAddExt.Multiplicative.theorem_4_43
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:48.920844+00:00
-- url     : https://prove2.me/theorems/5b688d6e-e59b-43d1-871f-08f59167865a
-- title:
--   Theorem 4.43 — robust errorless block condensers for samplable joint sources under H_NP
-- statement:
--   There is a universal constant $\delta>0$ such that the following holds. Assume $H_{NP}$. Then for every constant $0<\gamma\le 1$ and every $c_{\mathrm{size}}>1$, for every sufficiently large $n$ and all
--   $$n^\gamma\le k_y\le k_x\le n,\qquad (\log n)^2\le m\le k_y^{\delta},$$
--   there is an explicit polynomial-time function $\mathrm{rbCond}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$ that is a
--   $$\bigl(\lambda=2^{-m/4},\ k_y,\ k_y^{\ge}=k_x/2,\ k_x,\ k_{\mathrm{out}}=m/4\bigr)$$
--   robust errorless block condenser (Definition 4.32) for joint distributions on $\{0,1\}^n\times\{0,1\}^n$ samplable by deterministic circuits with postselection by nondeterministic circuits, both of size at most $n^{c_{\mathrm{size}}}$. Explicit: one polynomial-time machine (depending on $\gamma,c_{\mathrm{size}}$) computes $\mathrm{rbCond}(y,x)$ from $(\lfloor k_y\rfloor,\lfloor k_x\rfloor,m,y,x)$; $k_y,k_x$ are reals and $m$ an integer.
--
--   It is the main technical result of §9 and the building block of the errorless condenser of Theorem 4.42.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - encoding: explicit polynomial-time computable function → PolyTimeComputable f: Mathlib Turing.TM2ComputableInPolyTime over the alphabet Bool, and the family is the restriction of f to the relevant input lengths; reason: Mathlib's multi-stack Turing machine is polynomially equivalent to the multi-tape model
--   - encoding: E = ∪_c DTIME(2^{cn}); H_NP (Assumption 4.10) → InE f: a TM2 machine deciding f within 2^{c(ℓ+1)} steps for some c ∈ ℕ; HNP as in Assumption 4.10 with the circuits above; reason: ∪_c DTIME(2^{c(ℓ+1)}) = ∪_c DTIME(2^{cℓ}), and the union over c absorbs the polynomial overhead between machine models
--   - reading: "There exists a universal constant … Assume that E is hard …" → ∃ constant ∧ (HNP → …): the universal constant is chosen before, and independently of, the hard function; reason: the paper states the constant as universal and before the assumption
--   - encoding: distributions samplable by deterministic circuits with postselection by nondeterministic circuits, both of size at most s → IsPostselSamplable / IsJointPostselSamplable: Samp and Post each of size ≤ s, Post accepting some input, law (Samp(R) | Post(R) = 1); reason: Definitions 4.26–4.27 with the per-circuit bound the theorem states
--   - reading: an explicit polynomial-time function, for each admissible choice of the parameters → one polynomial-time machine f that receives (⌊k_y⌋, ⌊k_x⌋, m, y‖x) through pairEnc/unary and outputs the function value; reason: explicitness is read as one algorithm on discrete construction parameters; entropy thresholds remain real in the guarantee, and their integer parts index the construction; all relevant lengths are supplied separately
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 28 (PDF 32), Theorem 4.43; proof §9, pp. 49–59 (PDF 53–63)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_Hardness
import Definitions.Def_MultAddExt_Multiplicative_Sources

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Theorem 4.43** (Robust errorless block condensers under nondeterministic hardness), p. 28.
There is a universal `δ > 0` such that, assuming `H_NP`, for every `0 < γ ≤ 1` and `c_size > 1`,
for every sufficiently large `n` and every `n^γ ≤ k_y ≤ k_x ≤ n`, `(log n)² ≤ m ≤ k_y^δ`, there is
an explicit polynomial-time `rbCond : {0,1}ⁿ × {0,1}ⁿ → {0,1}^m` that is a
`(λ = 2^{−m/4}, k_y, k_y^≥ = k_x/2, k_x, k_out = m/4)` robust errorless block condenser for joint
distributions sampled with nondeterministic postselection, both circuits of size at most
`n^{c_size}`. One machine `f` computes `rbCond` from `(⌊k_y⌋, ⌊k_x⌋, m, y, x)`. -/
theorem theorem_4_43 : ∃ δ : ℝ, 0 < δ ∧ (HNP → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ csize : ℝ, 1 < csize →
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (ky kx : ℝ) (m : ℕ), (n : ℝ) ^ γ ≤ ky → ky ≤ kx → kx ≤ n →
      Real.logb 2 n ^ 2 ≤ m → (m : ℝ) ≤ ky ^ δ →
    ∃ rbCond : (Fin n → Bool) → (Fin n → Bool) → (Fin m → Bool),
      (∀ y x, f (pairEnc (unary ⌊ky⌋₊) (pairEnc (unary ⌊kx⌋₊)
          (pairEnc (unary m) (List.ofFn y ++ List.ofFn x)))) = List.ofFn (rbCond y x)) ∧
      IsRobustBlockCondenser rbCond (IsJointPostselSamplable n n ((n : ℝ) ^ csize))
        ((2 : ℝ) ^ (-(m : ℝ) / 4)) ky (kx / 2) kx ((m : ℝ) / 4)) := by sorry

end MultAddExt.Multiplicative
