-- Prove2me | Theorems.Thm_OAI_QuantumTrace_summable_polynomial_heat
-- name    : OAI.QuantumTrace.summable_polynomial_heat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:02:14.313478+00:00
-- url     : https://prove2.me/theorems/7a1aff21-fd02-4eb2-adeb-f6061106b529
-- title:
--   Heat-trace summability at half rate implies summability of quadratically weighted terms
-- statement:
--   Let $J$ be an arbitrary index set and let $u:J\to\mathbb{R}$ satisfy $u_j\ge 0$ for all $j$. If
--   $$\sum_{j\in J}e^{-u_j/2}<\infty,$$
--   then also
--   $$\sum_{j\in J}e^{-u_j}\big(1+u_j^2\big)<\infty .$$
--
--   In spectral terms, if the heat trace $\sum_je^{-tu_j}$ is finite at $t=1/2$, then at $t=1$ the second moment of the energy is finite as well. This is the kind of moment bound needed for Gibbs states built from a spectrum $(u_j)$.
--
--   **Formalization Note** Summability is unconditional summability (`Summable`) of real families.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/QuantumTrace/Basic.lean#L1360-L1382

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology

theorem OAI.QuantumTrace.summable_polynomial_heat {J : Type*} (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*(1+u j^2)) := by sorry
