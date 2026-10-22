-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_minimum_output_entropy_conjectures
-- name    : GuhaEPnI.MinOutput.minimum_output_entropy_conjectures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:07.966158+00:00
-- url     : https://prove2.me/theorems/b3618aeb-db97-4c49-84cd-f7a8db0970e0
-- title:
--   Minimum Output Entropy Conjectures 1–2, p. 3 — vacuum and thermal inputs attain the minimum
-- statement:
--   Let $n\ge1$, $\eta\in[0,1]$, and $K\ge0$. For two independent $n$-mode inputs to the beam splitter, both minimum output entropy statements have the same attained value:
--
--   $$\min S(\rho_c)=n\,g((1-\eta)K).$$
--
--   In Conjecture 1, the second input is thermal of mean $K$ per mode and the first ranges over zero-mean-field pure finite-energy states. Every corresponding output has entropy at least this value; the vacuum first input gives equality, and such an input and output exist.
--
--   In Conjecture 2, the first input is the vacuum and the second ranges over finite-energy states of entropy $n g(K)$. Every corresponding output has entropy at least the same value. A thermal second input is admissible, and together with the vacuum it attains equality.
--
--   This is the paper's two conjectures as consequences of its EPnI, whose formalization is already Proved and referenced separately.
--
--   **Formalization Note** The paper does not state finite energy explicitly. It is included for the optimized inputs because the referenced EPnI requires it and the published real-valued entropy returns a default value when its series diverges. The condition $n\ge1$ is required by Eq. (11).
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 3, Minimum Output Entropy Conjectures 1–2, Eqs. (16)–(17) and their proofs

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem minimum_output_entropy_conjectures (n : ℕ) (hn : 1 ≤ n)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (K : ℝ) (hK : 0 ≤ K) :
    ((∀ ρA ρB ρC : State n, IsPure ρA → IsZeroMeanField ρA → FiniteEnergy ρA →
        IsThermal K ρB → IsBeamSplitterOutput η ρA ρB ρC →
        (n : ℝ) * g ((1 - η) * K) ≤ entropy ρC) ∧
      (∀ ρA ρB ρC : State n, IsVacuum ρA → IsThermal K ρB → IsBeamSplitterOutput η ρA ρB ρC →
        entropy ρC = (n : ℝ) * g ((1 - η) * K)) ∧
      (∃ ρA ρB ρC : State n, IsVacuum ρA ∧ IsPure ρA ∧ IsZeroMeanField ρA ∧
        FiniteEnergy ρA ∧ IsThermal K ρB ∧ IsBeamSplitterOutput η ρA ρB ρC)) ∧
    ((∀ ρA ρB ρC : State n, IsVacuum ρA → FiniteEnergy ρB → entropy ρB = (n : ℝ) * g K →
        IsBeamSplitterOutput η ρA ρB ρC → (n : ℝ) * g ((1 - η) * K) ≤ entropy ρC) ∧
      (∀ ρB : State n, IsThermal K ρB → FiniteEnergy ρB ∧ entropy ρB = (n : ℝ) * g K)) := by sorry

end GuhaEPnI.MinOutput
