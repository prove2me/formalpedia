-- Prove2me | Theorems.Thm_OCB2012_cj_posSemidef_of_completelyPositive
-- name    : OCB2012.cj_posSemidef_of_completelyPositive
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T10:14:30.130741+00:00
-- url     : https://prove2.me/theorems/43e982aa-d24f-432f-84fa-c4ca8d28079b
-- title:
--   Choi: the CJ matrix of a completely positive map is positive semidefinite
-- statement:
--   Let $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$ be a linear map, with $X_1, X_2$ finite. If $\Phi$ is completely positive, then its CJ matrix is positive semidefinite:
--
--   $$M^{X_1X_2}\;\ge\;0 .$$
--
--   Here $J = M^{X_1X_2} = [\mathcal I\otimes\Phi(|\phi^+\rangle\langle\phi^+|)]^{T}$ is the Choi–Jamiołkowski (CJ) matrix of the linear map $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$, with $|\phi^+\rangle = \sum_j|jj\rangle$ unnormalized and ${}^T$ the full transpose (OCB p. 3). Entrywise, with indices ordered $X_1\times X_2$,
--
--   $$J_{(i,k),(j,l)} = \Phi\big(|j\rangle\langle i|\big)_{lk}.$$
--
--   Complete positivity means that $\Phi\otimes\mathrm{id}_n$ maps positive semidefinite matrices on $\mathbb C^{X_1}\otimes\mathbb C^n$ to positive semidefinite matrices, for every ancilla dimension $n$ (the ancilla is the second tensor factor, as in `PeresTerno.IsCompletelyPositive`). The proof applies this with $n = |X_1|$ to the unnormalized maximally entangled projector, and uses that transposition and reindexing preserve positivity. This is one direction of Choi's theorem; the paper uses it in the CPTP characterization on p. 4.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4 (CPTP iff M^{A1A2} >= 0 and Tr_{A2} M^{A1A2} = 1), the direction CP => M >= 0; M.-D. Choi, Completely positive linear maps on complex matrices, Linear Algebra Appl. 10, 285-290 (1975), https://doi.org/10.1016/0024-3795(75)90075-0, main theorem (complete positivity <=> positivity of the Choi matrix (Phi(E_ij))_{ij}); stated there for the untransposed Choi matrix, and transposition preserves positivity

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem cj_posSemidef_of_completelyPositive {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ)
    (hΦ : PeresTerno.IsCompletelyPositive Φ) : (cjMatrix Φ).PosSemidef := by sorry

end OCB2012
