-- Prove2me | Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
-- name    : ModularCurve.map_intCast_pow_char_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/8aa4b432-53c2-56c2-b8b4-6085b22c5837
-- title:
--   Frobenius on reductions of integral Laurent series: ̄ s(q)^ℓ=̄ s(q^ℓ)
-- statement:
--   Let $K$ be a commutative ring, let $\ell$ be a prime natural number, and assume $K$ has characteristic $\ell$. Let $s$ be a formal Laurent series with integer coefficients, i.e. an element of `LaurentSeries ℤ` $=$ `HahnSeries ℤ ℤ`, and write $\bar s$ for its coefficientwise image `s.map (Int.castRingHom K)` in `LaurentSeries K` under the canonical ring homomorphism $\mathbb{Z}\to K$. The assertion is the identity $\bar s^{\,\ell} = \mathrm{qExpand}\,K\,\ell\,(\bar s)$ in `LaurentSeries K`, where the left-hand side is the $\ell$-th power in the ring of Laurent series and $\mathrm{qExpand}\,K\,\ell$ is the ring homomorphism of `LaurentSeries K` obtained by embedding the exponent group $\mathbb{Z}$ into itself along multiplication by $\ell$ (an injective, strictly monotone additive map), that is, the substitution $q\mapsto q^{\ell}$: the coefficient of $q^{\ell m}$ in $\mathrm{qExpand}\,K\,\ell\,(\bar s)$ is the coefficient of $q^{m}$ in $\bar s$, and all coefficients in degrees not divisible by $\ell$ vanish. Thus $\bar s(q)^{\ell}=\bar s(q^{\ell})$ for every Laurent series with integral coefficients reduced into a ring of characteristic $\ell$.
--
--   This is the Frobenius congruence for $q$-expansions with integral coefficients: in characteristic $\ell$ raising a reduced integral $q$-expansion to the $\ell$-th power is the same as substituting $q^{\ell}$ for $q$, the identity underlying Kronecker-type congruences for modular functions such as $j$. It is used in the study of the modular curves of full level, in particular in the computations identifying the action of level automorphisms on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_intCast_pow_char_eq_qExpand.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.map_intCast_pow_char_eq_qExpand {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (s : LaurentSeries ℤ) :
    (s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K)) := by sorry
