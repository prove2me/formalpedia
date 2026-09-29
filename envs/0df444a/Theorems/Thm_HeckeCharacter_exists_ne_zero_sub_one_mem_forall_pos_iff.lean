-- Prove2me | Theorems.Thm_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff
-- name    : HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/88c3de87-221e-5f8f-aee8-c33e98fbdf90
-- title:
--   Integers ≡ 1 mod f with prescribed real signs
-- statement:
--   Let $K$ be a number field, let $\mathfrak f$ be an ideal of the ring of integers $\mathcal O_K$ with $\mathfrak f \neq 0$, and let $\varepsilon$ be an arbitrary predicate on the set of ring homomorphisms $\tau : K \to \mathbb R$ (that is, an arbitrary prescription of a truth value, hence of a sign, at each real embedding of $K$; no decidability or further structure on $\varepsilon$ is assumed). The assertion is that there exists an element $\beta \in \mathcal O_K$ such that $\beta \neq 0$, such that $\beta - 1$ lies in $\mathfrak f$, and such that for every ring homomorphism $\tau : K \to \mathbb R$ one has $0 < \tau(\beta)$ if and only if $\varepsilon(\tau)$ holds, where $\beta$ is viewed in $K$ via the inclusion $\mathcal O_K \subseteq K$. Thus the sign of $\beta$ at each real place is exactly the prescribed one, and simultaneously $\beta \equiv 1 \pmod{\mathfrak f}$. Note that the equivalence is an honest biconditional, so negative values are also forced where $\varepsilon$ fails.
--
--   This is the standard existence statement underlying ray class group and sign-character computations: every prescribed element of $\{\pm 1\}^{\text{real places}}$ is realised by a nonzero integer congruent to $1$ modulo a given nonzero modulus. It is used in the construction of Hecke characters of finite order with prescribed behaviour at the archimedean and uniformiser idèles, via [`HeckeCharacter.exists_isAdjuster`](thm.html#HeckeCharacter.exists_isAdjuster) and [`HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod`](thm.html#HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (ε : (K →+* ℝ) → Prop) :
    ∃ β : 𝓞 K, β ≠ 0 ∧ β - 1 ∈ 𝔣 ∧ ∀ τ : K →+* ℝ, (0 < τ (β : K) ↔ ε τ) := by sorry
