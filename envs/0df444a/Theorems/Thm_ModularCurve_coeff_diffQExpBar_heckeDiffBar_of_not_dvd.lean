-- Prove2me | Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd
-- name    : ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/ff6b27be-9e5a-5f84-b5b5-fba3e7edb25b
-- title:
--   q-expansion of the Hecke correspondence on differentials, ℓ∤ N
-- statement:
--   Let $N\ge 1$ and let $\ell$ be a prime with $\ell\nmid N$. Write $F_N$ for `modularFunctionFieldBar N`, the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ obtained as `laurentBaseChange` of `modularFunctionFieldFull N` $=\mathbb Q(\mathrm{divisorExpansions}\,N)\subseteq\mathrm{LaurentSeries}(\mathbb Q)$, i.e. the field generated over $\overline{\mathbb Q}$ by the coefficientwise image of that field of $q$-expansions. Assume `HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ`: the underlying ring homomorphism of the $\overline{\mathbb Q}$-algebra map `heckeBetaBar`, from the level-$N$ base-changed field into the level-$N\ell$ one, is integral. Let $\omega$ be a Kähler differential in $\Omega[F_N/\overline{\mathbb Q}]$ and $n\in\mathbb Z$. Let $\Theta=$ `diffQExpBar N` be the $F_N$-linear map $\Omega[F_N/\overline{\mathbb Q}]\to\mathrm{LaurentSeries}(\overline{\mathbb Q})$ induced by the derivation `qEulerOn` $(=q\,d/dq)$, and let $T=$ `heckeDiffBar N ⟨ℓ, _⟩` be the $\overline{\mathbb Q}$-linear endomorphism of $\Omega[F_N/\overline{\mathbb Q}]$ given by `Differential.correspondence` of the pair (`heckeBetaBar`, `heckeAlphaBar`) at level $N,\ell$. Then the $n$-th Laurent coefficient of $\Theta(T\omega)$ equals the $(n\ell)$-th coefficient of $\Theta\omega$ plus $\ell$ times the $(n/\ell)$-th coefficient of $\Theta\omega$ when $\ell\mid n$, and plus $0$ otherwise.
--
--   This identifies the action of the $\ell$-th Hecke correspondence on differentials of the modular function field, read off in $q$-expansions, with the weight-two Hecke operator $a_n\mapsto a_{n\ell}+\ell\,a_{n/\ell}$ on Laurent coefficients, in the case $\ell\nmid N$. It feeds the comparison of the Hecke algebra acting on regular differentials with its action on weight-two cusp forms, in particular the injectivity of the cotangent representation and the vanishing of Hecke polynomials on the relevant modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_not_dvd (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExpBar N (ModularCurve.heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n =
      (ModularCurve.diffQExpBar N ω).coeff (n * ℓ) +
        (ℓ : AlgebraicClosure ℚ) *
          (if (ℓ : ℤ) ∣ n then (ModularCurve.diffQExpBar N ω).coeff (n / ℓ) else 0) := by sorry
