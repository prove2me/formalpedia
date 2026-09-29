-- Prove2me | Theorems.Thm_ModularCurve_jqNModC_mul_pow_eq_pow
-- name    : ModularCurve.jqNModC_mul_pow_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0b213bce-2350-52c5-891a-1cbcfa3a4765
-- title:
--   Frobenius collapse: ̄ j(q^{Nℓ^k})=̄ j(q^N)^{ℓ^k}
-- statement:
--   Let $K$ be a commutative ring, let $N$ be a natural number with $N \neq 0$, let $\ell$ be a natural number which is prime and such that $K$ has characteristic $\ell$, and let $k$ be a natural number. Write $\bar j(q) =$ `jqModC K` for the element $q^{-1}\cdot \sum_n a_n q^n$ of the Laurent series field $K((q))$ obtained as the product of the Hahn series $q^{-1}$ (the monomial `HahnSeries.single (-1 : ℤ) 1`) with the power series `jNum` of integral coefficients, its coefficients mapped into $K$ along the canonical ring homomorphism $\mathbb{Z} \to K$; and for $M \neq 0$ write `jqNModC K M` for the image of $\bar j(q)$ under `qExpand K M`, the ring endomorphism of $K((q))$ obtained by multiplying all exponents by $M$, i.e. the substitution $q \mapsto q^{M}$. The assertion is the equality $$\mathrm{jqNModC}\ K\ (N\ell^{k}) = \big(\mathrm{jqNModC}\ K\ N\big)^{\ell^{k}}$$ in $K((q))$, that is, $\bar j(q^{N\ell^{k}}) = \bar j(q^{N})^{\ell^{k}}$. No field or reducedness hypothesis on $K$ is imposed.
--
--   This is the $q$-expansion form of the statement that, modulo $\ell$, one branch of the degeneracy map $X_0(N\ell) \to X_0(N)$ is the Frobenius; it is the computational input for the collapse of the modular function fields at levels divisible by powers of $\ell$. It is used in the construction of reductions of modular curves at level structures and in the analysis of the arithmetic Frobenius action on special places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqNModC_mul_pow_eq_pow.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.jqNModC_mul_pow_eq_pow (K : Type*) [CommRing K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (k : ℕ) :
    jqNModC K (N * ℓ ^ k) = (jqNModC K N) ^ (ℓ ^ k) := by sorry
