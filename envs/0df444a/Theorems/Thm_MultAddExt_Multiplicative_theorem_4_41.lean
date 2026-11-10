-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_theorem_4_41
-- name    : MultAddExt.Multiplicative.theorem_4_41
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:48:53.753651+00:00
-- url     : https://prove2.me/theorems/37d9a628-03bd-4cc7-8ab3-0282fa89186b
-- title:
--   Theorem 4.41 (= Theorem 4) — multiplicative extractors for min-entropy n^α samplable sources under nondeterministic hardness
-- statement:
--   There is a universal constant $\kappa>0$ (the paper's $\delta_{\mathrm{out}}^2/(8c_{\mathrm{IExt}})$) such that the following holds. Assume that E is hard for exponential-size nondeterministic circuits ($H_{NP}$). For every constant $0<\alpha\le 1$, let $\alpha'=\kappa\alpha$. For all constants $c_{\mathrm{size}}>1$ and $c_\varepsilon>0$ there are one deterministic polynomial-time Turing machine and an $n_0$ such that for every $n\ge n_0$ the machine computes a function
--   $$\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m,\qquad m=\lceil n^{\alpha'}\rceil,$$
--   that is an $(n^\alpha,n^{-c_\varepsilon})$-multiplicative extractor for distributions samplable by deterministic circuits with postselection by nondeterministic circuits, both of size at most $n^{c_{\mathrm{size}}}$: for every such source $X=(\mathrm{Samp}(R)\mid\mathrm{Post}(R)=1)$ with $\Pr[\mathrm{Post}(R)=1]>0$ and $H_\infty(X)\ge n^\alpha$, and every $\sigma\in\{0,1\}^m$,
--   $$\Pr[\mathrm{Ext}(X)=\sigma]\le e^{\,n^{-c_\varepsilon}}\cdot 2^{-m}.$$
--
--   This is the formal version of the paper's headline Theorem 4: under a worst-case hardness assumption for nondeterministic circuits, polynomially many nearly uniform bits can be extracted from efficiently samplable sources of polynomially small min-entropy, with a multiplicative (relative-error) guarantee. Theorem 4 follows by taking $c_{\mathrm{size}}=c_\varepsilon=c$: every source with $H_\infty\ge k\ge n^\alpha$ has $H_\infty\ge n^\alpha$, and $m\ge n^{\alpha'}\ge k^{\alpha'}$.
--
--   The unrestricted real constants and exact rounded lengths are retained from the literal uniform reading of the source; the computability issue this raises is recorded in insight I2, without adding a computability hypothesis or changing the stated lengths.
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - encoding: explicit polynomial-time computable function → PolyTimeComputable f: Mathlib Turing.TM2ComputableInPolyTime over the alphabet Bool, and the family is the restriction of f to the relevant input lengths; reason: Mathlib's multi-stack Turing machine is polynomially equivalent to the multi-tape model
--   - encoding: E = ∪_c DTIME(2^{cn}); H_NP (Assumption 4.10) → InE f: a TM2 machine deciding f within 2^{c(ℓ+1)} steps for some c ∈ ℕ; HNP as in Assumption 4.10 with the circuits above; reason: ∪_c DTIME(2^{c(ℓ+1)}) = ∪_c DTIME(2^{cℓ}), and the union over c absorbs the polynomial overhead between machine models
--   - reading: "For every constant 0 < α ≤ 1 there exists a constant α′ > 0, depending only on α … One may take α′ = αδ_out²/(8c_IExt), where δ_out and c_IExt are the universal constants" → ∃ κ > 0 before H_NP and before α, with α′ = κα; reason: the paper's explicit choice of α′ with universal constants; it is the stronger reading of "α′ depending only on α"
--   - reading: m = n^{α′} → m = ⌈n^{α′}⌉; reason: a bit length is integral, so the exact length uses a ceiling; truncation preserves the multiplicative bound, but computing an exact rounded real power is a separate uniformity issue recorded in insight I2
--   - reading: "for all sufficiently large n. There is an explicit polynomial-time computable function Ext" → one machine f and one n₀, fixed after α, c_size, c_ε, with Ext_n the restriction of f to {0,1}^n for every n ≥ n₀; reason: explicitness is uniformity over n; the machine may depend on the constants
--   - encoding: distributions samplable by deterministic circuits with postselection by nondeterministic circuits, both of size at most s → IsPostselSamplable / IsJointPostselSamplable: Samp and Post each of size ≤ s, Post accepting some input, law (Samp(R) | Post(R) = 1); reason: Definitions 4.26–4.27 with the per-circuit bound the theorem states
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 27 (PDF 31), Theorem 4.41 (headline Theorem 4, p. 5, PDF 9); proof §10, pp. 59–70 (PDF 63–74)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_Hardness
import Definitions.Def_MultAddExt_Multiplicative_Sources

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Theorem 4.41** (Multiplicative extractors under nondeterministic hardness), p. 27 — the formal
version of Theorem 4 (p. 5). There is a universal `κ > 0` (the paper's `δ_out²/(8c_IExt)`) such
that, assuming `H_NP`, for every `0 < α ≤ 1`, with `α' = κα`, and all `c_size > 1`, `c_ε > 0`, one
deterministic polynomial-time machine computes, for all sufficiently large `n`, a function
`Ext : {0,1}ⁿ → {0,1}^m`, `m = ⌈n^{α'}⌉`, that is an `(n^α, n^{−c_ε})`-multiplicative extractor for
distributions sampled by deterministic circuits with postselection by nondeterministic circuits, both
of size at most `n^{c_size}`: `Pr[Ext(X) = σ] ≤ e^{n^{−c_ε}} · 2^{−m}` for every such `X` with
`H∞(X) ≥ n^α` and every `σ ∈ {0,1}^m`. -/
theorem theorem_4_41 : ∃ κ : ℝ, 0 < κ ∧ (HNP →
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ csize : ℝ, 1 < csize → ∀ cε : ℝ, 0 < cε →
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ Ext : (Fin n → Bool) → (Fin ⌈(n : ℝ) ^ (κ * α)⌉₊ → Bool),
      (∀ x, f (List.ofFn x) = List.ofFn (Ext x)) ∧
      IsMultExtractor Ext (IsPostselSamplable n ((n : ℝ) ^ csize)) ((n : ℝ) ^ α)
        ((n : ℝ) ^ (-cε))) := by sorry

end MultAddExt.Multiplicative
