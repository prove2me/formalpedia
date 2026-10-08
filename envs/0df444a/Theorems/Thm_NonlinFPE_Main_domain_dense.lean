-- Prove2me | Theorems.Thm_NonlinFPE_Main_domain_dense
-- name    : NonlinFPE.Main.domain_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:57.179771+00:00
-- url     : https://prove2.me/theorems/9d402da8-298a-41f1-b3f6-4096feb4088a
-- title:
--   §3.1, p. 9 — under (H1)–(H3), C₀^∞(ℝ^d) ⊂ D(A), hence D(A) is dense in L¹
-- statement:
--   Assume (H1)–(H3) and let $A$ be the operator (3.8)–(3.9) on $L^1(\mathbb R^d)$. Then every test function $\varphi \in C_0^\infty(\mathbb R^d)$ belongs to $D(A)$, and
--   $$\overline{D(A)} = L^1(\mathbb R^d).$$
--
--   Density of the domain is what allows the Crandall–Liggett theorem to be applied to every initial datum $u_0 \in L^1$.
--
--   **Formalization Note** A test function is taken as an element of $L^1$ through its integrability; membership in $D(A)$ is the existence of $v \in L^1$ with $Au = v$ in the graph sense.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3.1, p. 9 ("Moreover, since C₀^∞(ℝ^d) ⊂ D(A), it follows that D(A) is dense in L¹.")

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz HunterPDE.Shared

/-- §3.1, p. 9, under (H1)–(H3): `C₀^∞(ℝᵈ) ⊂ D(A)` (every test function, as an element of `L¹`,
lies in the domain of the operator `A` of (3.8)–(3.9)), and `D(A)` is dense in `L¹`. -/
theorem domain_dense {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) :
    (∀ φ : SDEState d → ℝ, IsTestFunction Set.univ φ → ∀ hφ : Integrable φ volume,
      ∃ v, opA a b (hφ.toL1 φ) v) ∧
    Dense {u : SDEState d →₁[volume] ℝ | ∃ v, opA a b u v} := by sorry

end NonlinFPE.Main
