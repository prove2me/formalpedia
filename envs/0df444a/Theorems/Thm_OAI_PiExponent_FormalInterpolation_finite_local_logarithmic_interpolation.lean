-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_local_logarithmic_interpolation
-- name    : OAI.PiExponent.FormalInterpolation.finite_local_logarithmic_interpolation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:11:44.508988+00:00
-- url     : https://prove2.me/theorems/1d4716ba-85db-4492-a03a-63281efcffc2
-- title:
--   Local logarithmic interpolation on arbitrary finite coefficient sets
-- statement:
--   Let $m$ be a nonnegative integer, let $c\in\mathbb C^m$, and let $S$ be any finite set of exponent vectors in $\mathbb N^{m+1}$. Write $\Phi_c$ for the formal substitution
--
--   $$
--   X_0\mapsto 1+z_0,\qquad X_{i+1}\mapsto c_i+z_{i+1}+\log(1+z_0).
--   $$
--
--   Every family of complex coefficients indexed by $S$ is realized by the substituted image of a polynomial:
--
--   $$
--   \forall y:S\to\mathbb C,\quad \exists P\in\mathbb C[X_0,\ldots,X_m],\quad [z^a]\Phi_c(P)=y(a)\quad(a\in S).
--   $$
--
--   No degree bound or closure condition on $S$ is imposed. This is the local algebraic interpolation component of finite logarithmic packet interpolation.
--
--   **Formalization Note.** This finite-index adaptation of the source's weighted packet theorem retains an arbitrary finite subset of coefficients; the empty set and $m=0$ are included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean, triangularMap_comp_inverse, truncatedFormalJet_inverse, and formalJet_packet_surjective (lines 43-58, 105-115, 181-202). Finite-index adaptation: restrict a positive uniform-weight packet large enough to contain S.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.finite_local_logarithmic_interpolation
    {m : ℕ} (c : Fin m → ℂ) (S : Finset (Fin (m + 1) → ℕ)) :
    ∀ y : ↥S → ℂ, ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : ↥S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet c P) = y a := by sorry
