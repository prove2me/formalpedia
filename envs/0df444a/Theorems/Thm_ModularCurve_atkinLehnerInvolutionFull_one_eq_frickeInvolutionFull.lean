-- Prove2me | Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
-- name    : ModularCurve.atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/cf8f153b-9b99-5a9e-9ed3-6f54d0b28ba6
-- title:
--   At level one, the Atkin–Lehner involution at q is Fricke
-- statement:
--   Let $q$ be a prime. Write $F(M)$ for the intermediate field $\mathbb{Q} \subseteq F(M) \subseteq \mathbb{Q}((t))$ obtained by adjoining to $\mathbb{Q}$ the family `divisorExpansions M` inside the Laurent series field, and for $d \mid M$ let $j_d \in F(M)$ denote the element whose underlying Laurent series is `qExpand ℚ d jq`. The partial Atkin–Lehner involution `atkinLehnerInvolutionFull N ℓ` is defined to be, if one exists, a choice of $\mathbb{Q}$-algebra automorphism $\sigma$ of $F(N\ell)$ with $\sigma(j_d) = j_{d\ell}$ and $\sigma(j_{d\ell}) = j_d$ for every nonzero $d \mid N$, and the identity otherwise; the Fricke involution `frickeInvolutionFull M` is defined to be, if one exists, a choice of $\mathbb{Q}$-algebra automorphism $\sigma$ of $F(M)$ with $\sigma(j_a) = j_b$ for every factorisation $ab = M$ into nonzero factors, and the identity otherwise. The assertion is the equality of automorphisms of $F(1 \cdot q)$: `atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q)`.
--
--   This identifies the classical Atkin–Lehner involution $w_q$ on the full modular function field at level $q$ with the Fricke involution $w_N$ in the case $N = q$. It is used in the subsequent analysis of the pair of valuation subrings of the full modular function field at a prime level and in the comparison of the induced geometric automorphism with the Fricke involution on the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull.lean

import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
    (q : ℕ) [Fact q.Prime] :
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by sorry
