-- Prove2me | Theorems.Thm_LPRRingLWE_Clear_exists_preimage
-- name    : LPRRingLWE.Clear.exists_preimage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:53.707313+00:00
-- url     : https://prove2.me/theorems/c4936e15-6347-4dcc-8b28-6018af2db929
-- title:
--   Proof of Lemma 2.15, p. 17 — for c ∈ t·I⁻¹ with c ≡ 1 mod J and v ∈ IM: c·v ∈ t·M and c·v − v ∈ IJM
-- statement:
--   Let $K$ be a number field with ring of integers $R = \mathcal{O}_K$, let $I, J \subseteq R$ be ideals with $I \neq 0$, let $t \in I$, and let $M$ be a fractional ideal of $K$. Suppose $c \in K$ satisfies $c \in t\cdot I^{-1}$ and $c - 1 \in J$. Then for every $v \in IM$:
--   1. $c\cdot v \in t\cdot M$, i.e. $c\cdot v = t\cdot w$ for some $w \in M$;
--   2. $c \cdot v - v \in IJM$.
--
--   In display form,
--   $$\forall v \in IM:\qquad \bigl(\exists\, w \in M,\ c v = t w\bigr) \ \text{ and }\ c v - v \in IJM .$$
--
--   This is the surjectivity half of Lemma 2.15: $w$ is a preimage of $v \bmod IJM$ under $u \mapsto t u \bmod IJM$. Such a $c$ exists whenever $t\cdot I^{-1}$ is coprime to $J$ (apply the coprimality criterion of Lemma 2.13 to $t\cdot I^{-1}$ and $J$).
--
--   **Formalization Note** The element $c$ is taken as a hypothesis, so no coprimality assumption is needed. The paper computes $c$ "using the algorithm from Lemma 2.13"; the algorithm is not formalized. The paper's convention that $J$ and $M$ are nonzero is not assumed.
-- source:
--   Lyubashevsky, Peikert & Regev, On ideal lattices and learning with errors over rings, J. ACM 60(6) (2013), p. 17, proof of Lemma 2.15, third paragraph ("Let v ∈ IM be arbitrary … preimage of v mod IJM")

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

namespace LPRRingLWE.Clear

open NumberField
open scoped nonZeroDivisors

/-- Proof of Lemma 2.15, p. 17 (surjectivity step): given `c ∈ t · I⁻¹` with `c ≡ 1 mod J`,
every `v ∈ IM` satisfies `c · v ∈ t · M` and `c · v − v ∈ IJM`. -/
theorem exists_preimage {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I) (M : FractionalIdeal (𝓞 K)⁰ K)
    (c : K) (hc : c ∈ cleared t I) (hc1 : c - 1 ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ∀ v ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * M,
      (∃ w ∈ M, c * v = algebraMap (𝓞 K) K t * w) ∧
        c * v - v ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * J * M := by sorry

end LPRRingLWE.Clear
