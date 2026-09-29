-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitSeries_mem_modularFunctionField
-- name    : ModularCurve.sharpUnitSeries_mem_modularFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/0d0514eb-d138-58b9-82e5-42ea40d386eb
-- title:
--   The sharp η-quotient series lies in the function field of X₀(ℓ)
-- statement:
--   Let $\ell$ be a prime and suppose the invariance hypothesis [`ModularCurve.SharpUnitInvariant ℓ`](def/ModularCurve_EtaQuotient.html#L97) holds, i.e. that for every $\gamma \in \Gamma_0(\ell)$ and every $\tau$ in the upper half-plane one has $\mathrm{sharpUnitFun}\,\ell\,(\gamma\cdot\tau) = \mathrm{sharpUnitFun}\,\ell\,(\tau)$, where [`ModularCurve.sharpUnitFun ℓ`](def/ModularCurve_EtaQuotient.html#L73) is the function $\tau \mapsto \bigl(\eta(\tau)/\eta(M_\ell\cdot\tau)\bigr)^{e}$ with $M_\ell$ the Hecke diagonal matrix [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21) and $e =$ `sharpExp ℓ`. Then the formal Laurent series [`ModularCurve.sharpUnitSeries ℓ`](def/ModularCurve_EtaQuotient.html#L85) over $\mathbb{Q}$ — namely $q^{-n_\ell}$ times the power series `etaProdPow ℓ` (the $e$-th power of the eta product `etaProd`, coefficients pushed into $\mathbb{Q}$), divided by the image of `etaProdPow ℓ` under the ring homomorphism `qExpand ℚ ℓ` which multiplies all exponents by $\ell$, where $n_\ell = (\ell-1)/\gcd(\ell-1,12)$ is `eisensteinNumerator ℓ` — belongs to [`ModularCurve.modularFunctionField ℓ`](def/ModularCurve_X0.html#L250), the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansion `jq` of $j$ together with its image under `qExpand ℚ ℓ`.
--
--   This is the statement that, granted $\Gamma_0(\ell)$-invariance of the sharp eta quotient $(\eta(\tau)/\eta(\ell\tau))^{24/\gcd(\ell-1,12)}$, its $q$-expansion is a modular function for $\Gamma_0(\ell)$, i.e. lies in $\mathbb{Q}(j, j_\ell)$, the function field of $X_0(\ell)$ realised inside $\mathbb{Q}((q))$. It feeds the construction of the modular unit used in [`ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor`](thm.html#ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor), the principality of a multiple of the cuspidal divisor on $X_0(\ell)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitSeries_mem_modularFunctionField.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hW : ModularCurve.SharpUnitInvariant ℓ) : ModularCurve.sharpUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ := by sorry
