-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_valid_configurations
-- name    : KramersHubbard.PartitionFunction.valid_configurations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:46.789582+00:00
-- url     : https://prove2.me/theorems/d64fcd04-8524-461d-9766-3480c3faa6d9
-- title:
--   Lemma 12 — Valid-state mass (corrected: zero-coupling threshold)
-- statement:
--   For an attractive Kramers input, $\beta>0$, $M\ge1$ and $0<\lambda<1$, let $L$ and $L_\lambda$ be the concrete Trotter products and $Z_0=\operatorname{Tr}e^{-\beta H_0}$. Then
--
--   $$\operatorname{Tr}L^M\le e^{\beta\sum_iU_i}Z_0,\qquad\operatorname{Tr}L_\lambda^M=Z_0Z_\lambda,\qquad\pi_\lambda(A=B)=\frac{\operatorname{Tr}L^M}{\operatorname{Tr}L_\lambda^M}.$$
--
--   If
--
--   $$8\lambda M\beta\left(\sum_i\sqrt{U_i}\right)^2\le e^{-\delta\sum_iU_i},$$
--
--   then $\operatorname{Tr}L_\lambda^M\le2\operatorname{Tr}L^M$ and $\pi_\lambda(A=B)\ge1/2$. All three traces are positive real numbers. This controls the valid configurations without excluding zero couplings or empty interaction lists.
--
--   Differences from the source:
--   - encoding: complex Fock operators and one-based mode labels → occupation-basis matrices and zero-based Fin labels, with complex equalities to explicit real witnesses where needed; reason: the occupation basis is the entire Fock space, including the vacuum, and preserves the ordered CAR conventions
--   - correction: Eq.(67) divides by 8 M beta (sum sqrt(U_i))^2, which is undefined when all U_i=0 → the threshold is cross-multiplied as 8 lambda M beta (sum sqrt(U_i))^2 <= exp(-delta sum U_i); reason: N=r=M=beta=1, h=0, v_1=e_1, Theta(z_1,z_2)=(-conj(z_2),conj(z_1)), U_1=0 satisfies Definition 1 but the printed denominator is zero; L_lambda=L and all conclusions hold for every allowed lambda
--   - encoding: Lemma 12 uses the trace and valid-mass identities established in Eqs.(39)-(40) → those identities and positive real trace witnesses accompany both bounds; reason: the concrete law and pairing product are computed independently; these equalities are conclusions rather than hypotheses
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 12, p.31, proof p.32; Eqs.(39)-(40), p.17; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Worm

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 12, pp.31-32, with Eqs.(39)-(40), p.17. The divided threshold is
    cross-multiplied to retain the source's zero-interaction instances. -/
theorem valid_configurations {N r M : ℕ} (D : Data N r) (hD : Attractive D)
    (β : ℝ) (hβ : 0 < β) (hM : 0 < M) (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) :
    ∃ z0 zL zPair mass : ℝ,
      freeZ D β = (z0 : ℂ) ∧ trotterZ D β M = (zL : ℂ) ∧
      pairingZ D β M lam = (zPair : ℂ) ∧
      validMass (green (M := M) D β) lam = (mass : ℂ) ∧
      0 < z0 ∧ 0 < zL ∧ 0 < zPair ∧
      pairingZ D β M lam = freeZ D β * wormNormalizer (green (M := M) D β) lam ∧
      mass = zL / zPair ∧ zL ≤ Real.exp (β * ∑ i, D.U i) * z0 ∧
      (8 * lam * M * β * (∑ i, Real.sqrt (D.U i))^2 ≤
        Real.exp (-delta β M * ∑ i, D.U i) → zPair ≤ 2*zL ∧ 1/2 ≤ mass) := by sorry

end KramersHubbard.PartitionFunction
