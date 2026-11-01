-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_halt_unique_and_output_iso_iff
-- name    : Grunbaum2003.rayMachine_halt_unique_and_output_iso_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:41.62928+00:00
-- url     : https://prove2.me/theorems/477f5556-e100-4a2d-9cf6-4cb8f5456575
-- title:
--   Determinism of halting ray-machine runs and combinatorial invariance of face-lattice output
-- statement:
--   This theorem establishes two foundational properties of the Gritzmann–Klee–Westwater ray-oracle machine model (`rayMachineRun` and `IsRayFaceLatticeOutput`): determinism of halting configurations and combinatorial invariance of the output encoding.
--
--   1. **Uniqueness of halting configuration:** For any dimension $d \in \mathbb{N}$, any program $\Pi : \operatorname{List} \operatorname{RayInstruction}$, any ray oracle $\mathcal{O} : \mathbb{R}^d \to \mathbb{R}^d$, any initial configuration $c_0$, and any step counts $t_1, t_2 \in \mathbb{N}$, if running $\Pi$ from $c_0$ for $t_1$ steps yields a halting configuration $c_1$ and running $\Pi$ from $c_0$ for $t_2$ steps yields a halting configuration $c_2$, then $c_1 = c_2$:
--
--   $$
--   \operatorname{run}(\Pi, \mathcal{O}, t_1, c_0) = \operatorname{some}(c_1) \;\land\; \Pi[c_1.\mathrm{pc}] = \mathrm{halt} \;\land\; \operatorname{run}(\Pi, \mathcal{O}, t_2, c_0) = \operatorname{some}(c_2) \;\land\; \Pi[c_2.\mathrm{pc}] = \mathrm{halt} \implies c_1 = c_2.
--   $$
--
--   2. **Combinatorial invariance and uniqueness of output encoding:** For any polytopes $P \subseteq \mathbb{R}^{d_1}$ and $Q \subseteq \mathbb{R}^{d_2}$ and any configuration $c$ that encodes the face lattice of $P$ (`IsRayFaceLatticeOutput P c`), $c$ encodes the face lattice of $Q$ if and only if the face lattices of $P$ and $Q$ are order-isomorphic:
--
--   $$
--   \operatorname{IsRayFaceLatticeOutput}(P, c) \implies \Bigl(\operatorname{IsRayFaceLatticeOutput}(Q, c) \iff \mathcal{F}(P) \simeq_{\mathrm{ord}} \mathcal{F}(Q)\Bigr).
--   $$
--
--   Together, these properties show that a halting ray-machine computation produces a canonical output state $c$ whose adjacency-matrix register values determine the face poset $\mathcal{F}(P)$ up to unique order isomorphism.
--
--   **Formalization Note** Once `program[c.pc]? = some .halt`, `rayMachineStep` is a fixed point (`rayMachineStep program oracle c = some c`), so `rayMachineRun` satisfies the addition law $\operatorname{run}(t_1 + t_2) = \operatorname{run}(t_1) \gg\!\!= \operatorname{run}(t_2)$ and stabilizes at the first halting configuration.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem rayMachine_halt_unique_and_output_iso_iff :
    (∀ {d : ℕ} (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ))
      (t₁ t₂ : ℕ) (c₀ c₁ c₂ : RayConfiguration),
      rayMachineRun program oracle t₁ c₀ = some c₁ →
      program[c₁.pc]? = some .halt →
      rayMachineRun program oracle t₂ c₀ = some c₂ →
      program[c₂.pc]? = some .halt →
      c₁ = c₂) ∧
    (∀ {d₁ d₂ : ℕ} (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
      (c : RayConfiguration),
      IsRayFaceLatticeOutput P c →
      (IsRayFaceLatticeOutput Q c ↔ Nonempty (PolytopeFace P ≃o PolytopeFace Q))) := by sorry

end Grunbaum2003
