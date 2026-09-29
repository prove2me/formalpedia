-- Prove2me | Theorems.Thm_ModularCurve_phiIrreducible_of_prime
-- name    : ModularCurve.phiIrreducible_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a48fd1a5-57c7-5845-bfb5-c06ad1c39155
-- title:
--   Irreducibility of prime-level modular polynomial data
-- statement:
--   Let $p$ be a prime and let `data` be an element of `ModularPolynomialData p`, that is: a polynomial $\Phi$ in `Polynomial (Polynomial ℤ)` (a polynomial in one variable whose coefficients are integer polynomials) which is monic, whose degree in the outer variable equals `dedekindPsi p`, the sum of $p/d$ over the squarefree divisors $d$ of $p$, and which satisfies $\Phi.\mathrm{eval}_2\,(\mathtt{evalAtJ})\,(\mathtt{jqN }p)=0$: substituting the Laurent series `jqN p` for the outer variable and applying to each coefficient the ring homomorphism `evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ` that evaluates an integer polynomial at the series `jq` yields $0$ in `LaurentSeries ℚ`. The conclusion is `PhiIrreducible data`, i.e. the polynomial `data.toAdjoin`, obtained from $\Phi$ by mapping each coefficient through `evalAtJGen` into the intermediate field $\mathbb{Q}\langle\mathtt{jq}\rangle = \mathbb{Q}(\mathtt{jq}) \subseteq \mathtt{LaurentSeries }\mathbb{Q}$, is irreducible in `Polynomial ℚ⟮jq⟯`. Thus every prime-level datum, not merely some chosen one, gives an irreducible polynomial over $\mathbb{Q}(j)$.
--
--   This is the classical irreducibility of the modular polynomial $\Phi_N$ over $\mathbb{Q}(j)$, in the case of prime level $N=p$, where the degree $\psi(p)=p+1$ is forced. It is used for the uniqueness statement [`ModularCurve.modularPolynomialData_phi_unique_of_prime`](thm.html#ModularCurve.modularPolynomialData_phi_unique_of_prime) and, via [`ModularCurve.phiIrreducible_all`](thm.html#ModularCurve.phiIrreducible_all), for the irreducibility at general level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_phiIrreducible_of_prime.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.phiIrreducible_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : PhiIrreducible data := by sorry
