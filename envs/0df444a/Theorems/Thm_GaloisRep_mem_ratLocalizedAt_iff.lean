-- Prove2me | Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff
-- name    : GaloisRep.mem_ratLocalizedAt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/e6426615-3520-5555-af87-17bec96cedd8
-- title:
--   Membership in ℤ₍ₚ₎ via denominators
-- statement:
--   Let $p$ be a natural number assumed prime, and let $q$ be a rational number. The subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ is by definition the set of rationals whose reduced denominator is coprime to $p$, equipped with its subring structure (closure under multiplication, addition, negation and containing $0$ and $1$, each verified from the divisibility relations between the denominator of a product or sum and the product of the denominators). The theorem asserts the equivalence: $q$ lies in [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) if and only if $p$ does not divide the denominator `q.den` of $q$ in lowest terms. Thus for prime $p$ the defining coprimality condition on the denominator is restated as a plain non-divisibility condition, identifying the carrier of [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) with the usual localisation $\mathbb{Z}_{(p)}$ of $\mathbb{Z}$ at the prime $p$, viewed inside $\mathbb{Q}$.
--
--   This is the elementary characterisation of membership in the local ring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$; the primality of $p$ is exactly what turns coprimality of the denominator to $p$ into non-divisibility by $p$. It is used in the treatment of finite flat group schemes over $\mathbb{Z}_{(p)}$ entering the flatness condition on $p$-adic Galois representations, for instance by the comparison with the $p$-adic absolute value and by the statements about ring homomorphisms out of [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) attached to Hopf algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_mem_ratLocalizedAt_iff.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.mem_ratLocalizedAt_iff
    {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ¬ p ∣ q.den := by sorry
