-- Prove2me | Theorems.Thm_OAI_Solenoidal_periodic_integral_divergence_zero_C1
-- name    : OAI.Solenoidal.periodic_integral_divergence_zero_C1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:45.238108+00:00
-- url     : https://prove2.me/theorems/828de501-c81d-4934-a118-438f863bc9d2
-- title:
--   The divergence of a periodic $C^1$ field integrates to zero over the period cell
-- statement:
--   Call a function $g:\mathbb{R}^3\to E$, with values in a real normed space $E$, *periodic $C^1$* if it is differentiable on $\mathbb{R}^3$, each partial derivative $x\mapsto\partial_kg(x)=Dg(x)[e_k]$ ($k=0,1,2$, where $e_0,e_1,e_2$ is the standard basis) is continuous, and $g(x+10k)=g(x)$ for all $x\in\mathbb{R}^3$ and $k\in\mathbb{Z}^3$; that is, $g$ is a $C^1$ function on the torus $\mathbb{R}^3/10\mathbb{Z}^3$. Integrals over the fundamental cell $[0,10)^3$ are taken with respect to Lebesgue measure.
--
--   **Theorem.** Let $E$ be a real normed space and let $g_0,g_1,g_2:\mathbb{R}^3\to E$ be periodic $C^1$. Then
--   $$\int_{[0,10)^3}\sum_{j=0}^{2}\partial_jg_j(x)\,dx=0 .$$
--
--   In words, the divergence of a $C^1$ vector field on the flat torus has zero integral, also when the three components take values in a general normed space $E$. This is the basic integration-by-parts tool on the periodic domain; it yields the vanishing of the integral of a single partial derivative, periodic integration by parts, and the cancellation of transport and pressure terms in energy identities.
--
--   **Formalization Note** The three conditions form the structure `TorusC1 g`; the partial derivative is `fderiv ℝ g x (basis j)` and the integral is the Bochner integral over `fundamentalCell`. No completeness of $E$ is assumed; for incomplete $E$ the Bochner integral is $0$ by Lean's convention, so the content of the statement lies in the case of Banach spaces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/ClassicalRegularity.lean#L103-L123

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem OAI.Solenoidal.periodic_integral_divergence_zero_C1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Fin 3 → Space → E) (hg : ∀ j, TorusC1 (g j)) :
    (∫ x in fundamentalCell, ∑ j : Fin 3, fderiv ℝ (g j) x (basis j)) = 0 := by sorry
