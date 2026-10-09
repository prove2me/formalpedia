-- Prove2me | Theorems.Thm_LPRRingLWE_Clear_lemma_2_15
-- name    : LPRRingLWE.Clear.lemma_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:51.469111+00:00
-- url     : https://prove2.me/theorems/9e52e001-17b8-4441-b60c-1b99b3a9303b
-- title:
--   Lemma 2.15, p. 17 — for t ∈ I with t·I⁻¹ coprime to J, u ↦ t·u induces an R-module isomorphism M/JM → IM/IJM
-- statement:
--   Let $K$ be a number field with ring of integers $R = \mathcal{O}_K$, let $I, J \subseteq R$ be nonzero ideals, let $t \in I$ be such that the ideal $t\cdot I^{-1} \subseteq R$ is coprime to $J$ (that is, $t\cdot I^{-1} + J = R$), and let $M$ be a nonzero fractional ideal of $K$. Consider the $R$-linear map
--   $$\theta_t : M \longrightarrow IM/IJM, \qquad u \longmapsto t\cdot u \bmod IJM .$$
--   Then $\theta_t$ is surjective and its kernel is exactly $JM$. Equivalently, multiplication by $t$ induces an isomorphism of $R$-modules
--   $$M/JM \;\xrightarrow{\ \sim\ }\; IM/IJM, \qquad u \bmod JM \longmapsto t u \bmod IJM .$$
--
--   The lemma lets one replace an arbitrary ideal $I$ by the ring $R$ itself modulo $q$: with $J = \langle q\rangle$ and $M = R$ it identifies $R/qR$ with $I/qI$, and with $M = I^\vee$ it identifies $I^\vee/qI^\vee$ with $R^\vee/qR^\vee$. Both reductions of the paper (§4.2 and §5) rest on these identifications.
--
--   **Formalization Note** The paper's sentence "Moreover, this isomorphism may be efficiently inverted given $I, J, M$, and $t$" is algorithmic and is not formalized. The hypotheses $I \neq 0$, $J \neq 0$, $M \neq 0$ express the paper's convention that ideals are nonzero (footnote 2, p. 13); $I \neq 0$ is essential because Lean sets $0^{-1} = 0$. The isomorphism is stated through the given map (surjectivity and kernel), not as the bare existence of some isomorphism, which would hold for unrelated reasons.
-- source:
--   Lyubashevsky, Peikert & Regev, On ideal lattices and learning with errors over rings, J. ACM 60(6) (2013), p. 17, Lemma 2.15

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

namespace LPRRingLWE.Clear

open NumberField
open scoped nonZeroDivisors

/-- Lemma 2.15, p. 17: for `t ∈ I` with `t · I⁻¹` coprime to `J` and a fractional ideal `M`,
the map `M → IM/IJM`, `u ↦ t · u mod IJM`, is surjective with kernel `JM`; that is,
`θ_t(u) = t · u` induces an `𝓞 K`-module isomorphism `M/JM ≅ IM/IJM`. -/
theorem lemma_2_15 {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I)
    (hcop : ClearedCoprime t I J) (M : FractionalIdeal (𝓞 K)⁰ K) (hM : M ≠ 0) :
    Function.Surjective (theta t I J ht M) ∧
      LinearMap.ker (theta t I J ht M) = sub M ((J : FractionalIdeal (𝓞 K)⁰ K) * M) := by sorry

end LPRRingLWE.Clear
