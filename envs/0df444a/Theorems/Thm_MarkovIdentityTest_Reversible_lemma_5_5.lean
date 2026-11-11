-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_5_5
-- name    : MarkovIdentityTest.Reversible.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:12.626684+00:00
-- url     : https://prove2.me/theorems/c7a78eff-2e90-4fd0-b3d9-7f2779491dc8
-- title:
--   Lemma 5.5 — the observable score: $Z_t\ge\mathrm{Fluc}_t+\sum_iN_i(t)H^2(P_i,Q_i)-\mathrm{Rem}_t$, $\mathbb E\,\mathrm{Rem}_T\le 23n$, $\mathbb E\,\mathrm{Fluc}_T^2\le 54n^2$
-- statement:
--   Let $P,Q$ be stochastic and $M\ge1$. Let $Z_t$ be the observable score and $\mathrm{Fluc}_t=\sum_{i:L_i(t)\ge1}U_{v_i}(q_i;D_i(t))/L_i(t)$ the capped-weight retained score on the enlarged alphabet (supported destinations of $P_i$ with weights $1/P_{ij}$, plus one extra outcome of reference probability $0$, $Q$-probability $\sum_{j:P_{ij}=0}Q_{ij}$ and weight $M$; $v_i$ capped, $q_i$ the enlarged row of $Q$). Then there is a nonnegative function $\mathrm{Rem}_t$ of the prefix such that on every length-$t$ prefix whose transitions all lie in the support of $P$
--   $$Z_t\ge\mathrm{Fluc}_t+\sum_iN_i(t)H^2(P_i,Q_i)-\mathrm{Rem}_t,$$
--   and, at an independent positive geometric time $T$ of mean $M$, from every initial state,
--   $$\mathbb E_Q\mathrm{Rem}_T\le23n,\qquad\mathbb E_Q[\mathrm{Fluc}_T^2]\le54n^2,$$
--   both expectations being finite. $Q$ need not be reversible or rapidly mixing.
--
--   Differences from the source:
--
--   - encoding: Fluc_t, named in the lemma and defined in its proof (pp. 29–30) → the explicit definition `fluctuation` on the enlarged alphabet Option (Fin n); reason: the lemma's statement uses the proof's definition; unsupported `some j` entries have weight, mass and count 0
--   - reading: Rem_t, the proof-only nonnegative remainder → ∃ Rem ≥ 0, a function of the prefix, the same for every initial state; reason: the paper names Rem_t without a closed form in the statement (its proof builds it from Lemma 5.4's existential Rem_i plus t/(8M)); a single Rem for all initial states is the stronger reading and what the proof gives
--   - encoding: E_Q at the geometric time T of mean M → series over t with absolute convergence asserted; M ∈ ℝ, M ≥ 1; reason: same law; integrability rules out a default value 0
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 29, Lemma 5.5 (Fluc_t and Rem_t defined in the proof, pp. 29–30)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Lemma 5.5 (Jia, p. 29 / PDF 31): `Fluc_t` is the explicit capped-weight score of the proof;
`Rem_t` is a nonnegative function of the prefix, the same for every initial state. -/
theorem lemma_5_5 {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : IsStochastic P)
    (hQ : IsStochastic Q) (M : ℝ) (hM : 1 ≤ M) :
    ∃ Rem : (t : ℕ) → (Fin (t + 1) → Fin n) → ℝ,
      (∀ t ω, 0 ≤ Rem t ω) ∧
      (∀ (t : ℕ) (ω : Fin (t + 1) → Fin n), SupportedPrefix P ω →
        fluctuation M P Q ω + ∑ i, (departures ω i : ℝ) * hellingerSq (P i) (Q i) - Rem t ω
          ≤ observableScore P ω) ∧
      ∀ x : Fin n,
        GeomIntegrable M Q x Rem ∧
        geomExp M Q x Rem ≤ 23 * n ∧
        GeomIntegrable M Q x (fun _ ω => fluctuation M P Q ω ^ 2) ∧
        geomExp M Q x (fun _ ω => fluctuation M P Q ω ^ 2) ≤ 54 * (n : ℝ) ^ 2 := by sorry

end MarkovIdentityTest.Reversible
