-- Prove2me | Theorems.Thm_ModularCurve_full_eq_of_prime
-- name    : ModularCurve.full_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/31fa1d0a-3ebe-5b18-9f60-eed47b096057
-- title:
--   At prime level the two modular function fields agree
-- statement:
--   Let $\ell$ be a natural number, nonzero, and assume $\ell$ is prime. Two intermediate fields of $\mathbb{Q}$ inside the field of Laurent series $\mathrm{LaurentSeries}\,\mathbb{Q}$ are compared. Here `qExpand ℚ N` denotes the ring endomorphism of Laurent series obtained by transporting along multiplication by $N$ on the exponent group $\mathbb{Z}$, that is, the substitution $q \mapsto q^{N}$, and `jq` is the Laurent series serving as the $q$-expansion of $j$. The field `modularFunctionFieldFull ℓ` is the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the set `divisorExpansions ℓ` of all series `qExpand ℚ d jq` with $d$ a nonzero natural number dividing $\ell$, while `modularFunctionField ℓ` is the subfield generated over $\mathbb{Q}$ by the two elements `jq` and `qExpand ℚ ℓ jq`. The theorem asserts that for prime $\ell$ these two intermediate fields are equal: adjoining the $q$-expansions $j(q^{d})$ for all divisors $d$ of $\ell$ yields nothing beyond $\mathbb{Q}(j(q), j(q^{\ell}))$.
--
--   This identifies, at prime level, the "all divisors" presentation of the function field attached to $X_0(\ell)$ with the two-generator presentation $\mathbb{Q}(j(q), j(q^{\ell}))$, so that results stated for the two-generator field may be applied to the full field. It is used throughout the algebraic development of $X_0(\ell)$ in this project, for instance in the analysis of the cuspidal classes and of the Fricke involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_full_eq_of_prime.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.full_eq_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ := by sorry
