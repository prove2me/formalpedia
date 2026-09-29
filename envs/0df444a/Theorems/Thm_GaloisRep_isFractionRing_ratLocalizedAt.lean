-- Prove2me | Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
-- name    : GaloisRep.isFractionRing_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/72903496-4bd1-5797-945f-69aa305c1503
-- title:
--   ℚ is the fraction field of `ratLocalizedAt p`
-- statement:
--   Let $p$ be a natural number, and let [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbb{Q}$ whose elements are exactly those rationals $q$ whose denominator $q.\mathrm{den}$ (the positive denominator of the reduced representation) is coprime to $p$; closure under multiplication, addition, negation and the presence of $0$ and $1$ come from the divisibility of the denominator of a product or sum by the product of the denominators. The theorem asserts that the inclusion of this subring into $\mathbb{Q}$ exhibits $\mathbb{Q}$ as its field of fractions in Mathlib's sense, that is, the structure map is a localisation of [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) at its submonoid of non-zero-divisors. No hypothesis is imposed on $p$: for $p$ prime the subring is $\mathbb{Z}_{(p)}$, for $p=0$ the condition on denominators forces $q.\mathrm{den}=1$ and the subring is $\mathbb{Z}$, for $p=1$ it is all of $\mathbb{Q}$, and for composite $p$ it is the semilocal ring of rationals whose denominators avoid the prime divisors of $p$; in every case the conclusion is that $\mathbb{Q}$ is the fraction field.
--
--   This is the statement $\operatorname{Frac}(\mathbb{Z}_{(p)})=\mathbb{Q}$ in the form of a fraction-field instance for the coefficient ring used in the flatness-at-$p$ condition. It is invoked throughout the treatment of integral models and finite flat group schemes over [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), where the generic fibre is taken over the fraction field $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isFractionRing_ratLocalizedAt.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.isFractionRing_ratLocalizedAt (p : ℕ) :
    IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ := by sorry
