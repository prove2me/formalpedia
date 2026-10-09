-- Prove2me | Theorems.Thm_OCB2012_exists_kraus_of_cj_posSemidef
-- name    : OCB2012.exists_kraus_of_cj_posSemidef
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T10:14:25.930232+00:00
-- url     : https://prove2.me/theorems/ef5dcba4-ada7-493c-944c-f097528c7443
-- title:
--   Choi: a positive semidefinite CJ matrix yields a Kraus decomposition $\Phi(\rho) = \sum_m K_m\rho K_m^\dagger$
-- statement:
--   Let $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$ be a linear map, with $X_1, X_2$ finite. If its CJ matrix is positive semidefinite, $M^{X_1X_2}\ge 0$, then $\Phi$ has a Kraus decomposition with at most $|X_1|\,|X_2|$ operators: there are $|X_2|\times|X_1|$ matrices $K_m$, indexed by $m\in X_1\times X_2$, such that
--
--   $$\Phi(\rho) = \sum_{m} K_m\,\rho\,K_m^\dagger\qquad\text{for every }\rho .$$
--
--   Here $J = M^{X_1X_2} = [\mathcal I\otimes\Phi(|\phi^+\rangle\langle\phi^+|)]^{T}$ is the Choi–Jamiołkowski (CJ) matrix of the linear map $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$, with $|\phi^+\rangle = \sum_j|jj\rangle$ unnormalized and ${}^T$ the full transpose (OCB p. 3). Entrywise, with indices ordered $X_1\times X_2$,
--
--   $$J_{(i,k),(j,l)} = \Phi\big(|j\rangle\langle i|\big)_{lk}.$$
--
--   The right-hand side is `PeresTerno.krausUpdate K ρ` (Peres–Terno Eq. (6)). Combined with the fact that maps of Kraus form are completely positive (`PeresTerno.krausUpdate_completelyPositive`), this gives the converse direction of Choi's theorem, $M^{X_1X_2}\ge0\Rightarrow\Phi$ completely positive, used in the CPTP characterization on p. 4 of OCB 2012.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4 (CPTP iff M^{A1A2} >= 0 and Tr_{A2} M^{A1A2} = 1), the direction M >= 0 => CP; M.-D. Choi, Completely positive linear maps on complex matrices, Linear Algebra Appl. 10, 285-290 (1975), https://doi.org/10.1016/0024-3795(75)90075-0, main theorem and its proof (Kraus form Phi(A) = sum_i V_i^* A V_i obtained from a decomposition of the positive Choi matrix)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem exists_kraus_of_cj_posSemidef {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ)
    (hJ : (cjMatrix Φ).PosSemidef) :
    ∃ K : x1 × x2 → Matrix x2 x1 ℂ, ∀ ρ, Φ ρ = PeresTerno.krausUpdate K ρ := by sorry

end OCB2012
