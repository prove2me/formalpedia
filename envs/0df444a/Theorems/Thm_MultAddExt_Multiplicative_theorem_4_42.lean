-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_theorem_4_42
-- name    : MultAddExt.Multiplicative.theorem_4_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:54.86011+00:00
-- url     : https://prove2.me/theorems/29b04613-7d41-44fa-9f19-2ac5cb4fb44a
-- title:
--   Theorem 4.42 — errorless (n^γin, n^{γin·δout})-condensers to n^{γin/2} bits for samplable sources under H_NP
-- statement:
--   There is a universal constant $0<\delta_{\mathrm{out}}<1/2$ such that the following holds. Assume $H_{NP}$. Then for all constants $0<\gamma_{\mathrm{in}}\le 1$ and $c>1$ there is an explicit polynomial-time function
--   $$\mathrm{Cond}_{\gamma_{\mathrm{in}},c}:\{0,1\}^n\to\{0,1\}^{\lfloor n^{\gamma_{\mathrm{in}}/2}\rfloor}$$
--   such that for all sufficiently large $n$ and every source $X$ samplable by a deterministic circuit with postselection by a nondeterministic circuit, both of size at most $n^c$,
--   $$H_\infty(X)\ge n^{\gamma_{\mathrm{in}}}\implies H_\infty\bigl(\mathrm{Cond}_{\gamma_{\mathrm{in}},c}(X)\bigr)\ge n^{\gamma_{\mathrm{in}}\delta_{\mathrm{out}}}.$$
--   That is, it is an errorless $(n^{\gamma_{\mathrm{in}}},n^{\gamma_{\mathrm{in}}\delta_{\mathrm{out}}})$-condenser for this class (Definition 4.15). The machine may depend on $\gamma_{\mathrm{in}}$ and $c$; $\delta_{\mathrm{out}}$ does not.
--
--   The goal applies this condenser twice before the final extraction step.
--
--   The unrestricted real constants and exact rounded lengths are retained from the literal uniform reading of the source; the computability issue this raises is recorded in insight I2, without adding a computability hypothesis or changing the stated lengths.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - encoding: explicit polynomial-time computable function → PolyTimeComputable f: Mathlib Turing.TM2ComputableInPolyTime over the alphabet Bool, and the family is the restriction of f to the relevant input lengths; reason: Mathlib's multi-stack Turing machine is polynomially equivalent to the multi-tape model
--   - encoding: E = ∪_c DTIME(2^{cn}); H_NP (Assumption 4.10) → InE f: a TM2 machine deciding f within 2^{c(ℓ+1)} steps for some c ∈ ℕ; HNP as in Assumption 4.10 with the circuits above; reason: ∪_c DTIME(2^{c(ℓ+1)}) = ∪_c DTIME(2^{cℓ}), and the union over c absorbs the polynomial overhead between machine models
--   - reading: "There exists a universal constant … Assume that E is hard …" → ∃ constant ∧ (HNP → …): the universal constant is chosen before, and independently of, the hard function; reason: the paper states the constant as universal and before the assumption
--   - encoding: distributions samplable by deterministic circuits with postselection by nondeterministic circuits, both of size at most s → IsPostselSamplable / IsJointPostselSamplable: Samp and Post each of size ≤ s, Post accepting some input, law (Samp(R) | Post(R) = 1); reason: Definitions 4.26–4.27 with the per-circuit bound the theorem states
--   - reading: output length n^{γin/2} → ⌊n^{γin/2}⌋; reason: an output length is an integer; the floor is the stronger choice (a shorter output can be zero-padded without changing min-entropy)
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 28 (PDF 32), Theorem 4.42; proof §6.3

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_Hardness
import Definitions.Def_MultAddExt_Multiplicative_Sources

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Theorem 4.42** (Errorless condensers under nondeterministic hardness), p. 28. There is a
universal `0 < δ_out < 1/2` such that, assuming `H_NP`, for all `0 < γ_in ≤ 1` and `c > 1` there is
an explicit polynomial-time `Cond_{γ_in,c} : {0,1}ⁿ → {0,1}^{⌊n^{γ_in/2}⌋}` such that, for all
sufficiently large `n`, every source `X` sampled by a deterministic circuit with postselection by a
nondeterministic circuit, both of size at most `n^c`, satisfies
`H∞(X) ≥ n^{γ_in} ⟹ H∞(Cond_{γ_in,c}(X)) ≥ n^{γ_in δ_out}`. -/
theorem theorem_4_42 : ∃ δout : ℝ, 0 < δout ∧ δout < 1 / 2 ∧ (HNP →
    ∀ γin : ℝ, 0 < γin → γin ≤ 1 → ∀ c : ℝ, 1 < c →
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ Cond : (Fin n → Bool) → (Fin ⌊(n : ℝ) ^ (γin / 2)⌋₊ → Bool),
      (∀ x, f (List.ofFn x) = List.ofFn (Cond x)) ∧
      IsErrorlessCondenser Cond (IsPostselSamplable n ((n : ℝ) ^ c)) ((n : ℝ) ^ γin)
        ((n : ℝ) ^ (γin * δout))) := by sorry

end MultAddExt.Multiplicative
