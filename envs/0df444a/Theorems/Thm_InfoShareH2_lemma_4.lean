-- Prove2me | Theorems.Thm_InfoShareH2_lemma_4
-- name    : InfoShareH2.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:06.388203+00:00
-- url     : https://prove2.me/theorems/cdaebe6d-0ab8-49eb-a59f-a6d94f8baaaa
-- title:
--   Lemma 4 — under Assumption 2, $Q=\exp(\Theta)$ is an outer function in $H^2$
-- statement:
--   Let $\tilde\psi\in\tilde\Psi$ satisfy Assumption 2, and let
--
--   $$\Theta(z)=\frac1{2\pi}\int_{-\pi}^{\pi}\frac{e^{i\lambda}+z}{e^{i\lambda}-z}\log|\tilde\psi(e^{-i\lambda})|\,d\lambda,\qquad |z|<1.$$
--
--   Then $Q(z)=\exp(\Theta(z))$ is an outer function in $H^2$: there is a square-summable coefficient sequence $(q_n)$, outer in the sense of Definition 3, with $\sum_nq_nz^n=\exp(\Theta(z))$ for $|z|<1$.
--
--   The lemma justifies the parametrization of the outer factor by the coefficients $\theta_n$ of $\Theta$ used in Lemma 5 and in the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: "Under Assumption 2, Q = exp(Θ)" → ψ̃ ∈ Ψ̃ satisfying Assumption 2, with Θ the integral of p.27 built from ψ̃; reason: Θ is defined from ψ̃ on p.27; Assumption 1 is standing
--   - encoding: "Q is an outer function in H²" → ∃ q ∈ ℓ² outer (Definition 3) with ∑ q_n zⁿ = exp(Θ(z)) on D; reason: H² represented by coefficient sequences
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Lemma 4, p.27 (proof p.28)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Lemma 4.** SSRN 4319721 (v. 2024-01-20), Lemma 4, p.27 (proof p.28). "Under
Assumption 2, the function `Q(z) = exp(Θ(z))` is an outer function in `H²`."

`Θ` is the integral of p.27 built from `ψ̃`; the statement is for `ψ̃ ∈ Ψ̃` (Assumption 1, standing)
satisfying Assumption 2. "`Q ∈ H²` is outer" is: its coefficient sequence `q` lies in `ℓ²`, is outer
(Definition 3), and `∑ q_n zⁿ = exp(Θ(z))` on `D`. -/
theorem lemma_4 (ψ : ℕ → ℝ) (hψ : ψ ∈ PsiTilde) (hA2 : Assumption2 ψ) :
    ∃ q : ℕ → ℂ, IsOuter q ∧ ∀ z ∈ Disk, zTransform q z = exp (Theta ψ z) := by sorry

end InfoShareH2
