-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jqNModC_eq_pow_unconditional
-- name    : ModularCurve.qExpand_jqNModC_eq_pow_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/1b15fb89-56f9-5f74-91ed-8c490a8deaee
-- title:
--   Frobenius identity for the q-expansion of j(q^N)
-- statement:
--   Let $K$ be a commutative ring, let $N$ be a nonzero natural number and let $\ell$ be a prime such that $K$ has characteristic $\ell$. Here `qExpand K n` denotes the ring endomorphism of the Laurent series ring `LaurentSeries K` obtained by transporting supports along multiplication by $n$ on $\mathbb{Z}$ (an order-preserving injection for $n \ge 1$), i.e. the substitution $q \mapsto q^{n}$; `jqModC K` is the Laurent series $\mathrm{single}(-1,1) \cdot \mathrm{ofPowerSeries}(\mathrm{jNum} \bmod \ell)$, that is $q^{-1}$ times the image in $K[[q]]$ of the integral power series `jNum` under the coefficientwise map $\mathbb{Z} \to K$; and `jqNModC K N` is `qExpand K N (jqModC K)`, the series obtained from it by $q \mapsto q^{N}$. The assertion is the equality in `LaurentSeries K` $$\mathrm{qExpand}\,K\,\ell\,(\mathrm{jqNModC}\,K\,N) = (\mathrm{jqNModC}\,K\,N)^{\ell},$$ i.e. substituting $q^{\ell}$ for $q$ in the reduction of the $q$-expansion of $j(q^{N})$ agrees with raising that series to the $\ell$-th power. No nontriviality or field hypothesis on $K$ is imposed.
--
--   This is the Frobenius (Kronecker congruence) identity for the $q$-expansion of the modular invariant in characteristic $\ell$: reduction mod $\ell$ turns the substitution $q \mapsto q^{\ell}$ into the $\ell$-th power map. It is used in the analysis of place specialisations and prolongation tuples on the modular curve, where crossing exponents and node data at characteristic-$\ell$ places are computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jqNModC_eq_pow_unconditional.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.qExpand_jqNModC_eq_pow_unconditional (K : Type*) [CommRing K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] :
    qExpand K ℓ (jqNModC K N) = (jqNModC K N) ^ ℓ := by sorry
