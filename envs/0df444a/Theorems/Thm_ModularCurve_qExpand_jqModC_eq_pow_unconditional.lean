-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
-- name    : ModularCurve.qExpand_jqModC_eq_pow_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b852b094-d026-59b0-a6b0-e4f7cd340346
-- title:
--   Frobenius identity ̄ j(q^ℓ) = ̄ j(q)^ℓ in characteristic ℓ
-- statement:
--   Let $K$ be a commutative ring, $\ell$ a prime number, and suppose $K$ has characteristic $\ell$. Write $\bar j =$ `jqModC K` for the element of the Laurent series field `LaurentSeries K` given by $\mathrm{single}(-1,1)$ times the image under `HahnSeries.ofPowerSeries ℤ K` of the coefficientwise reduction along `Int.castRingHom K` of the integral power series `jNum` $=$ `eisenstein4 ^ 3 * dedekindEtaUnitInv`; thus $\bar j$ is $q^{-1}$ times the reduction in $K$ of the integral $q$-series $E_4^3\eta^{-24}$, i.e. the $q$-expansion of the modular $j$-invariant with its coefficients read in $K$. Write `qExpand K ℓ` for the ring endomorphism of `LaurentSeries K` obtained by transporting the support along multiplication by $\ell$ on $\mathbb{Z}$, that is, the substitution $q \mapsto q^{\ell}$. The assertion is the equality
--   $$\bar j(q^{\ell}) = \bar j(q)^{\ell}$$
--   in `LaurentSeries K`, i.e. `qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ`. No finiteness, perfectness or field hypothesis on $K$ is imposed.
--
--   This is the $q$-expansion identity underlying Kronecker's congruence for the modular polynomial $\Phi_\ell$ in characteristic $\ell$; no statement about $\Phi_\ell$ itself is made here. It serves the study of the mod-$\ell$ geometry of modular curves and their charts, and is cited widely in that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.qExpand_jqModC_eq_pow_unconditional (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ := by sorry
