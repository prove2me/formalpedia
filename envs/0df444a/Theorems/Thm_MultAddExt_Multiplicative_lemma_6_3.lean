-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_6_3
-- name    : MultAddExt.Multiplicative.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:49:16.060989+00:00
-- url     : https://prove2.me/theorems/6836887b-db48-44e8-9716-f773e299c41f
-- title:
--   Lemma 6.3 — basic errorless condenser from subsources of a samplable source, given a dependent second source
-- statement:
--   There is a universal constant $0<\delta\le 1/4$ such that, assuming $H_{NP}$, the following holds. For all constants $0<\alpha,\gamma\le 1$ and $c>1$, for all sufficiently large $n$ and all $n_a\in\mathbb N$ with $n_a\le n^\alpha$, setting $k=n^\gamma$, there is an explicit function $\mathrm{Cond}:\{0,1\}^{n_a}\times\{0,1\}^n\to\{0,1\}^m$, $m=\lfloor n^{\alpha-(1-\delta)\gamma}\rfloor$, with the following property. Let $(A,W)$ on $\{0,1\}^{n_a}\times\{0,1\}^n$ be samplable by size-$n^c$ circuits with postselection by size-$n^c$ nondeterministic circuits, and
--   $$(A,W)=(1-p)(A^{(0)},W^{(0)})+p\,(A_{\mathrm{good}},W_{\mathrm{good}})$$
--   for some $2^{-n^{\delta\gamma}/32}\le p\le 1$ and distributions $(A^{(0)},W^{(0)})$, $(A_{\mathrm{good}},W_{\mathrm{good}})$, where $H_\infty(A_{\mathrm{good}})\ge k$ and $H_\infty(W)\ge k$. Then
--   $$H_\infty\bigl(\mathrm{Cond}(A_{\mathrm{good}},W_{\mathrm{good}})\bigr)\ge n^{\delta\gamma/4}.$$
--   Explicit: one polynomial-time machine computes $\mathrm{Cond}(a,w)$ from the pair $(a,w)$.
--
--   It is the one-step condenser that Theorem 4.42 iterates.
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
--   - reading: output length m = n^{α−(1−δ)γ} → m = ⌊n^{α−(1−δ)γ}⌋; reason: an output length is an integer; the floor is the stronger choice, since a shorter output can be padded to a longer one without changing its min-entropy
--   - reading: an explicit function Cond : {0,1}^{n_a} × {0,1}^n → {0,1}^m → one polynomial-time machine f with f(⟨a, w⟩) = Cond(a, w) for all n ≥ n₀ and n_a ≤ n^α; reason: "explicit" means polynomial-time computable by one algorithm; the self-delimiting pair lets it read n_a and n
--   - encoding: the mixture (1 − p)(A^(0), W^(0)) + p(A_good, W_good) → distributions P0, Pgood with P = (1 − p)·P0 + p·Pgood pointwise and p ≤ 1; reason: a mixture of distributions has weight p ≤ 1
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 32 (PDF 36), Lemma 6.3

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
import Definitions.Def_MultAddExt_Multiplicative_Hardness
import Definitions.Def_MultAddExt_Multiplicative_Sources

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 6.3** (basic errorless condenser), p. 32. There is a universal `0 < δ ≤ 1/4` such that,
assuming `H_NP`, for all `0 < α, γ ≤ 1` and `c > 1`, for all sufficiently large `n` and all
`n_a ≤ n^α`, with `k = n^γ`, there is an explicit `Cond : {0,1}^{n_a} × {0,1}ⁿ → {0,1}^m`,
`m = ⌊n^{α − (1−δ)γ}⌋`, such that: if `(A, W)` is samplable by size-`n^c` circuits with postselection
by size-`n^c` nondeterministic circuits and `(A, W) = (1 − p)(A^(0), W^(0)) + p(A_good, W_good)` with
`p ≥ 2^{−n^{δγ}/32}`, `H∞(A_good) ≥ k` and `H∞(W) ≥ k`, then `H∞(Cond(A_good, W_good)) ≥ n^{δγ/4}`.
One machine `f` computes `Cond` from the pair `(a, w)`. -/
theorem lemma_6_3 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ (HNP →
    ∀ α γ : ℝ, 0 < α → α ≤ 1 → 0 < γ → γ ≤ 1 → ∀ c : ℝ, 1 < c →
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ na : ℕ, (na : ℝ) ≤ (n : ℝ) ^ α →
    ∃ Cond : (Fin na → Bool) → (Fin n → Bool) → (Fin ⌊(n : ℝ) ^ (α - (1 - δ) * γ)⌋₊ → Bool),
      (∀ a w, f (pairEnc (List.ofFn a) (List.ofFn w)) = List.ofFn (Cond a w)) ∧
      ∀ P : (Fin na → Bool) × (Fin n → Bool) → ℝ,
        IsJointPostselSamplable na n ((n : ℝ) ^ c) P →
        ∀ (p : ℝ) (P0 Pgood : (Fin na → Bool) × (Fin n → Bool) → ℝ),
          IsDist P0 → IsDist Pgood → p ≤ 1 → (2 : ℝ) ^ (-((n : ℝ) ^ (δ * γ)) / 32) ≤ p →
          (∀ z, P z = (1 - p) * P0 z + p * Pgood z) →
          (n : ℝ) ^ γ ≤ minEntropy (pushforward Prod.fst Pgood) →
          (n : ℝ) ^ γ ≤ minEntropy (pushforward Prod.snd P) →
          (n : ℝ) ^ (δ * γ / 4) ≤ minEntropy (pushforward (fun z => Cond z.1 z.2) Pgood)) := by sorry

end MultAddExt.Multiplicative
