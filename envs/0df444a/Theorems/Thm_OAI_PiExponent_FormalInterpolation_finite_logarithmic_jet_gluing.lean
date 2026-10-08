-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_gluing
-- name    : OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:11:38.550394+00:00
-- url     : https://prove2.me/theorems/d4f8b883-ecf8-4c29-a1cd-a56d4999d670
-- title:
--   Chinese remainder gluing of finite logarithmic jets
-- statement:
--   Let $J$ be a finite index type, let $c:J\to\mathbb C^m$ be injective, and let $S\subset\mathbb N^{m+1}$ be finite. For each $j\in J$, let $Q_j$ be a polynomial in $m+1$ variables. Write $\Phi_{c_j}$ for the substitution $X_0\mapsto1+z_0$ and $X_{i+1}\mapsto(c_j)_i+z_{i+1}+\log(1+z_0)$. There is a single polynomial $P$ agreeing with every prescribed local polynomial on the coefficients in $S$:
--
--   $$
--   \exists P\in\mathbb C[X_0,\ldots,X_m],\quad
--   [z^a]\Phi_{c_j}(P)=[z^a]\Phi_{c_j}(Q_j)\quad(j\in J,\ a\in S).
--   $$
--
--   This is the finite-jet Chinese remainder compatibility statement at distinct points $(1,c_j)$. It places no degree restriction on the global polynomial and does not require $S$ to be downward closed.
--
--   **Formalization Note.** This isolates the gluing step of the source's simultaneous packet-surjectivity proof. Arbitrary finite index sets are obtained by restricting a sufficiently large uniform-weight packet.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AffineJetPackets.lean, formalJet_packet_eq_of_sub_mem_pow and formalJet_packets_surjective (lines 13-50), especially Ideal.exists_forall_sub_mem_ideal and JetPowerIdealCoprime.powerIdeal_pow_pairwise_isCoprime. Finite-index adaptation of the gluing step, with no weighted-degree restriction.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.finite_logarithmic_jet_gluing
    {m : ℕ} {J : Type*} [Fintype J]
    (c : J → Fin m → ℂ) (hc : Function.Injective c)
    (S : Finset (Fin (m + 1) → ℕ))
    (Q : J → MvPolynomial (Fin (m + 1)) ℂ) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ j : J, ∀ a : ↥S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) (Q j)) := by sorry
