-- Prove2me | Theorems.Thm_LPRRingLWE_Clear_lemma_2_14
-- name    : LPRRingLWE.Clear.lemma_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:51.523128+00:00
-- url     : https://prove2.me/theorems/edb0ef49-10d0-4113-a13d-02f6861d475f
-- title:
--   Lemma 2.14, p. 16 — there exists t ∈ I such that t·I⁻¹ ⊆ R is coprime to J
-- statement:
--   Let $K$ be a number field with ring of integers $R = \mathcal{O}_K$, and let $I, J \subseteq R$ be nonzero ideals. Then there exists a nonzero $t \in I$ such that the fractional ideal $t\cdot I^{-1}$ is an integral ideal of $R$ coprime to $J$:
--   $$\exists\, t \in I\setminus\{0\}:\qquad t\cdot I^{-1} \subseteq R \quad\text{and}\quad t\cdot I^{-1} + J = R .$$
--
--   This is the "clearing" step: although $I$ need not be principal, it can be replaced by the principal ideal $\langle t \rangle = (t I^{-1})\cdot I$ up to a factor that is invisible modulo $J$. It supplies the element $t$ used in Lemma 2.15 and in step 1 of the reduction of §4.2.
--
--   **Formalization Note** The paper's clause "Moreover, such $t$ can be found efficiently given $I$ and the prime ideal factorization of $J$" is algorithmic and is not formalized. The hypotheses $I \neq 0$ and $J \neq 0$ are the paper's convention that ideals are nonzero (footnote 2, p. 13); $J \neq 0$ is necessary (for $J = 0$ the claim would say $I = \langle t\rangle$ is principal), and $I \neq 0$ prevents Lean's convention $0^{-1} = 0$ from changing the meaning of $t\cdot I^{-1}$. The conclusion $t \neq 0$ is the same convention applied to the ideal $t\cdot I^{-1}$ the page speaks of (it only matters for $J = R$, where $t = 0$ would otherwise be allowed).
-- source:
--   Lyubashevsky, Peikert & Regev, On ideal lattices and learning with errors over rings, J. ACM 60(6) (2013), p. 16, Lemma 2.14

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

namespace LPRRingLWE.Clear

open NumberField
open scoped nonZeroDivisors

/-- Lemma 2.14, p. 16 (existence clause): for nonzero ideals `I`, `J` of `𝓞 K` there is
`t ∈ I`, `t ≠ 0` (so that `t · I⁻¹` is a nonzero ideal, footnote 2), such that the ideal
`t · I⁻¹ ⊆ 𝓞 K` is coprime to `J`. -/
theorem lemma_2_14 {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ∃ t ∈ I, t ≠ 0 ∧ ClearedCoprime t I J := by sorry

end LPRRingLWE.Clear
