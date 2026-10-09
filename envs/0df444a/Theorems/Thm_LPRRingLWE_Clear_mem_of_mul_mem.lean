-- Prove2me | Theorems.Thm_LPRRingLWE_Clear_mem_of_mul_mem
-- name    : LPRRingLWE.Clear.mem_of_mul_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:43.819285+00:00
-- url     : https://prove2.me/theorems/70d78eb9-6be0-4a58-971e-75a0f07c3333
-- title:
--   Proof of Lemma 2.15, p. 17 — if t·I⁻¹ is coprime to J, u ∈ M and t·u ∈ IJM, then u ∈ JM
-- statement:
--   Let $K$ be a number field with ring of integers $R = \mathcal{O}_K$, let $I, J \subseteq R$ be ideals with $I \neq 0$, let $t \in I$ be such that $t\cdot I^{-1} \subseteq R$ is coprime to $J$, and let $M$ be a fractional ideal of $K$. Then for every $u \in M$,
--   $$t\cdot u \in IJM \ \Longrightarrow\ u \in JM .$$
--
--   This is the injectivity half of Lemma 2.15: the kernel of $u \mapsto t u \bmod IJM$ on $M$ is contained in $JM$ (the reverse inclusion $t\cdot JM \subseteq IJM$ is immediate from $t \in I$).
--
--   **Formalization Note** The paper's convention that $J$ and $M$ are nonzero is not needed for this implication and is not assumed; dropping it makes the statement stronger. $I \neq 0$ is kept because $I^{-1}$ appears in the coprimality hypothesis.
-- source:
--   Lyubashevsky, Peikert & Regev, On ideal lattices and learning with errors over rings, J. ACM 60(6) (2013), p. 17, proof of Lemma 2.15, second paragraph ("Second, if θ_t(u) = 0 … u ∈ JM")

import Mathlib
import Definitions.Def_LPRRingLWE_Clear_Setting

namespace LPRRingLWE.Clear

open NumberField
open scoped nonZeroDivisors

/-- Proof of Lemma 2.15, p. 17 (kernel step): if `t · I⁻¹` is coprime to `J`, `u ∈ M` and
`t · u ∈ IJM`, then `u ∈ JM`. -/
theorem mem_of_mul_mem {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (t : 𝓞 K) (ht : t ∈ I) (hcop : ClearedCoprime t I J)
    (M : FractionalIdeal (𝓞 K)⁰ K) :
    ∀ u ∈ M, algebraMap (𝓞 K) K t * u ∈ (I : FractionalIdeal (𝓞 K)⁰ K) * J * M →
      u ∈ (J : FractionalIdeal (𝓞 K)⁰ K) * M := by sorry

end LPRRingLWE.Clear
