-- Prove2me | Theorems.Thm_OAI_PiExponent_logJetSurjective_transverseForSpatialVolume_at
-- name    : OAI.PiExponent.logJetSurjective_transverseForSpatialVolume_at
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:40:55.693407+00:00
-- url     : https://prove2.me/theorems/13ab52aa-1904-4a51-bc6e-694d629cecce
-- title:
--   Restrict one finite logarithmic jet assignment to transverse jets
-- statement:
--   At a fixed truncation level H, logarithmic jet surjectivity implies transverse polynomial jet surjectivity with the same source support bound and strict target cutoff. The proof extends each spatial assignment by zero outside distinguished degree zero, then specializes the distinguished variable to its constant slice.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
open scoped BigOperators

theorem OAI.PiExponent.logJetSurjective_transverseForSpatialVolume_at
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex) (H : Nat)
    (hlog : OAI.PiExponent.logJetSurjective m K w0 v0 alpha w c H) :
    ∀ J : Fin K → (Fin m →₀ Nat) → Complex,
      ∃ Q : MvPolynomial (Fin m) Complex,
        (∀ e ∈ Q.support,
          (∑ i : Fin m, (w i : Real) * (e i : Real)) ≤ (H : Real)) ∧
        ∀ (j : Fin K) (e : Fin m →₀ Nat),
          (∑ i : Fin m, ((w i : Real) / (alpha : Real)) * (e i : Real)) < (H : Real) →
            MvPolynomial.coeff e
              (MvPolynomial.aeval (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) Q) = J j e := by sorry
