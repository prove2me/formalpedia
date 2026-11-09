-- Prove2me | Theorems.Thm_IPPComplexities_Unconditional_lemma_3_1
-- name    : IPPComplexities.Unconditional.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:07.688866+00:00
-- url     : https://prove2.me/theorems/4a41dfb0-cba2-46c0-8daa-a048562faa95
-- title:
--   Lemma 3.1 — description length of verification strategies for IPPs
-- statement:
--   There exist absolute positive integers $K_q,K_c,A,D$ with the following property. Let $L$ be any Boolean-string property, $\varepsilon>0$, and $V$ a valid IPP verifier family for $L$ at proximity $\varepsilon$, with worst-case query and bidirectional communication bounds $q(n),c(n)$. There is a family of finite binary descriptions $s_n$ for the fixed interpreter, defining another valid IPP $W_n=\operatorname{decode}_n(s_n)$ for the same $L$ and $\varepsilon$, such that, for every $n$,
--
--   $$Q_{W}(n)\le K_q q(n),\qquad C_{W}(n)\le K_c c(n),\qquad
--   |s_n|\le B_{A,D}(n,q(n)+c(n)).$$
--
--   Here $B_{A,D}(n,t)=(An)^{Dt}$ for $n\ge2,t>0$, with a constant allowance $A$ at $t=0$ and $\max\{n,2\}$ handling lengths zero and one. Both completeness and soundness retain the full $2/3$ guarantees. All constants precede the property, proximity, original system, resource functions, and length. The descriptions may vary nonuniformly with length. The original strategy laws may be nonrecursive and need not have finite descriptions.
--
--   This is the sole supporting milestone for the unconditional lower bound. It bounds the number of finitely describable replacement strategies while preserving the two resource bounds separately.
--
--   **Formalization Note** The decoder's syntax is fixed once for all systems. Zero-resource deterministic verdicts have five-bit codes, covered by the existential constant $A$; no numerical compression multiplier is asserted by the paper or hard-coded in the theorem.
--
--   Differences from the source:
--   - generalization: IPPs valid for every positive proximity, with the proximity then fixed for lower bounds → systems required to be valid only at the single proximity under consideration; reason: every full IPP restricts to such a system; the source argument at that proximity needs no validity elsewhere
--   - encoding: unrestricted private-coin oracle interaction → arbitrary laws on finite compatible private plans, with behavioral provers seeing only the public bit transcript; reason: finite external interaction can be unfolded with private correlations retained; public framing and perfect recall preserve the source model, and the operational bridge is a proof obligation rather than an added hypothesis
--   - encoding: poly(n)^{q(n)+c(n)} description bits and separate O(q), O(c) bounds → absolute positive Kq, Kc, A, D and the bound B_{A,D}, including constant verdict overhead at q+c=0; reason: this makes the asymptotic quantifiers explicit; unary framing and finite initial lengths are absorbed by the polynomial base and exponent without changing the positive-resource scale
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 7, Lemma 3.1; proof pp. 7–8 (PDF pp. 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_validity
import Definitions.Def_IPPComplexities_Unconditional_encoding

namespace IPPComplexities.Unconditional

/-- Lemma 3.1, with absolute separate resource factors and a fixed effective
language. Neither the original laws nor the family need be recursive. -/
theorem lemma_3_1 :
    ∃ Kq Kc A D : ℕ, 0 < Kq ∧ 0 < Kc ∧ 0 < A ∧ 0 < D ∧
      ∀ (L : Property) (ε : ℝ) (V : System) (q c : ℕ → ℕ),
        ValidAt L ε V → ResourceBounds V q c →
        ∃ code : ℕ → List Bool,
          ValidAt L ε (fun n => decode n (code n)) ∧
          ResourceBounds (fun n => decode n (code n))
            (fun n => Kq * q n) (fun n => Kc * c n) ∧
          ∀ n : ℕ, (code n).length ≤ descriptionBound A D n (q n + c n) := by sorry

end IPPComplexities.Unconditional
