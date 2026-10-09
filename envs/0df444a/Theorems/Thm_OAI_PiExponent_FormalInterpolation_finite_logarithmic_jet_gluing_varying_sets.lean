-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_gluing_varying_sets
-- name    : OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing_varying_sets
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T18:31:52.061193+00:00
-- url     : https://prove2.me/theorems/390370ef-320d-4b4f-aecb-92983e7f7607
-- title:
--   Finite logarithmic jet gluing for varying coefficient sets
-- statement:
--   Let $J$ be finite and let $c:J\to\mathbb C^m$ assign distinct centers. For each $j\in J$, choose a finite set $S_j\subset\mathbb N^{m+1}$ and a polynomial $Q_j$. Under the formal logarithmic substitution $\Phi_{c_j}$, there is one polynomial $P$ whose coefficients agree with those of $Q_j$ at every index selected for that center:
--
--   $$
--   \exists P,\qquad [z^a]\Phi_{c_j}(P)=[z^a]\Phi_{c_j}(Q_j)\quad(j\in J,\ a\in S_j).
--   $$
--
--   The coefficient sets may vary independently with the center. No degree bound or downward-closure condition is required.
-- source:
--   Finite-index adaptation of the logarithmic jet Chinese-remainder gluing argument in https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AffineJetPackets.lean, formalJet_packet_eq_of_sub_mem_pow and formalJet_packets_surjective.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing_varying_sets
    {m : ℕ} {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (S : J → Finset (Fin (m + 1) → ℕ))
    (Q : J → MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : J, ∀ a : {a // a ∈ S j},
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) (Q j)) := by sorry
