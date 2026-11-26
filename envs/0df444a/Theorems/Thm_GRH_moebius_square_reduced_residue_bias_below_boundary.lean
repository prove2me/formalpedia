-- Prove2me | Theorems.Thm_GRH_moebius_square_reduced_residue_bias_below_boundary
-- name    : GRH.moebius_square_reduced_residue_bias_below_boundary
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T11:53:32.437561+00:00
-- url     : https://prove2.me/theorems/ebfcf6de-c11b-4420-bb99-92e3875c1325
-- title:
--   Möbius deviation from the reduced-residue mean at perfect squares below the exponent boundary
-- statement:
--   For \(1/2<\sigma\le0.8749570698\), a modulus with at least two unit classes, and a unit residue \(a\), bound \(\lvert M_a(u^2)-P_q(u^2)/\varphi(q)\rvert\) by \(D(u^2+1)^\sigma\) uniformly over nonnegative integers \(u\). Here \(P_q\) is the sum of the Möbius function over all integers coprime to \(q\), and \(M_a\) restricts it to the class \(a\). The differences sum to zero over all unit residues.
-- source:
--   A modulus-specific subproblem of https://prove2.me/theorems/4267fa34-f5fc-4de7-a1fd-d4169b15fa7e obtained by subtracting the common average over the unit group.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.moebius_square_reduced_residue_bias_below_boundary
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (hmany : 1 < q.totient) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ := by sorry
