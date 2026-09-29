-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7b255209-b67c-5365-a1b4-fbd90b64f2e8
-- title:
--   Local degree one for Kummer generators that are local n-th powers
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an extension of $E$ that is Galois, and let $n$ be a natural number such that $E$ contains a primitive $n$-th root of unity (the set `primitiveRoots n E` is nonempty). Let $u \in E$ and $\alpha \in M$ satisfy $\alpha^n = u$ (the image of $u$ under the structure map $E \to M$), and assume that $\alpha$ generates $M$ in the sense that every $E$-algebra automorphism $\sigma$ of $M$ with $\sigma\alpha = \alpha$ is the identity. Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$, and assume that $u$ becomes an $n$-th power in the $v$-adic completion $E_v$, i.e. there is $b \in E_v$ with the image of $u$ in $E_v$ equal to $b^n$. Let $w$ be an extension of $v$ to $\mathcal{O}_M$, that is, a height-one prime of $\mathcal{O}_M$ whose contraction to $\mathcal{O}_E$ is $v$. Then the completion $M_w$ has rank $1$ as a module over $E_v$: $\operatorname{finrank}_{E_v} M_w = 1$.
--
--   This is the statement that a Kummer extension $M = E(\sqrt[n]{u})$, with $\mu_n \subseteq E$, splits completely at every finite place $v$ of $E$ at which $u$ is already an $n$-th power, the local degree $[M_w : E_v]$ being $1$ for each $w \mid v$. It is used in the algebraic treatment of the second inequality of class field theory, via [`NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots`](thm.html#NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots) and [`NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom`](thm.html#NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    {n : ℕ} (hζ : (primitiveRoots n E).Nonempty) (u : E) (α : M) (hα : α ^ n = algebraMap E M u)
    (hgen : ∀ σ : M ≃ₐ[E] M, σ α = α → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hb : ∃ b : v.adicCompletion E, algebraMap E (v.adicCompletion E) u = b ^ n)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    Module.finrank (v.adicCompletion E) (w.1.adicCompletion M) = 1 := by sorry
