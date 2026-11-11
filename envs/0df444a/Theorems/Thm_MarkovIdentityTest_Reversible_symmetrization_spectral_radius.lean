-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_symmetrization_spectral_radius
-- name    : MarkovIdentityTest.Reversible.symmetrization_spectral_radius
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:14.812898+00:00
-- url     : https://prove2.me/theorems/d99bfea7-297b-4954-a826-a92140b0fa12
-- title:
--   §6.2 — geometric symmetrization does not increase the spectral radius: $\rho(\tilde A)\le\rho(A)$, $\tilde A_{ij}=\sqrt{A_{ij}A_{ji}}$
-- statement:
--   For every square matrix $A$ with nonnegative real entries, its geometric symmetrization $\tilde A_{ij}=\sqrt{A_{ij}A_{ji}}$ satisfies
--   $$\rho(\tilde A)\le\rho(A),$$
--   with $\rho$ the spectral radius over the complex spectrum. The paper uses it for the affinity matrix $A=A(P,Q)$, which need not be symmetric because $Q$ is arbitrary (cited to Kingman 1961, Elsner–Johnson–Dias da Silva 1988).
--
--   Differences from the source:
--
--   - generalization: A = A(P, Q), the affinity matrix of Lemma 6.2's proof → any entrywise nonnegative real square matrix; reason: the printed claim is the general fact the paper cites; it specializes to A(P, Q)
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 32, §6.2, proof of Lemma 6.2

import Mathlib
import Definitions.Def_RobustToDynamics_specRadius
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy

set_option autoImplicit false

namespace MarkovIdentityTest.Reversible

/-- §6.2, proof of Lemma 6.2 (Jia, p. 32 / PDF 34): the geometric symmetrization of an entrywise
nonnegative square matrix does not increase the (complex) spectral radius. -/
theorem symmetrization_spectral_radius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) :
    RobustToDynamics.specRadius (geometricSymmetrization A) ≤ RobustToDynamics.specRadius A := by sorry

end MarkovIdentityTest.Reversible
