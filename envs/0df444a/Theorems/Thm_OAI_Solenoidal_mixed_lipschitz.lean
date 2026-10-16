-- Prove2me | Theorems.Thm_OAI_Solenoidal_mixed_lipschitz
-- name    : OAI.Solenoidal.mixed_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:56:52.273983+00:00
-- url     : https://prove2.me/theorems/29edb36f-0218-47c4-acb2-ccc37c2ba784
-- title:
--   Lipschitz constants for mixed space-time derivatives from bounds on the next-order derivatives
-- statement:
--   Let space-time $\mathbb{R}\times\mathbb{R}^3$ carry the norm $\|(t,x)\|=\max\big(|t|,\max_i|x_i|\big)$ and let $\mathbb{R}^3$ carry the maximum norm $\|\cdot\|_\infty$. Index the space-time coordinates by $j\in\{0,1,2,3\}$, where $j=0$ is time and $j=1,2,3$ are the spatial coordinates $x_0,x_1,x_2$, and let $e_0=(1,0)$, $e_1=(0,b_0)$, $e_2=(0,b_1)$, $e_3=(0,b_2)$ be the corresponding unit vectors, where $b_0,b_1,b_2$ is the standard basis of $\mathbb{R}^3$.
--
--   Let $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, $(t,x)\mapsto u(t,x)$, be a time-dependent vector field that is $C^\infty$ jointly in $(t,x)$. For a finite word $a=(a_1,\dots,a_k)$ over the alphabet $\{0,1,2,3\}$, the mixed derivative $\partial^a u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ is defined recursively by $\partial^{\varnothing}u=u$ for the empty word and
--
--   $$
--   \partial^{ja}u(z)=D\big(\partial^{a}u\big)(z)\,[e_j],
--   $$
--
--   where $ja$ is the word obtained by putting the letter $j$ in front of $a$; thus $\partial^{(a_1,\dots,a_k)}u=\partial_{a_1}\partial_{a_2}\cdots\partial_{a_k}u$.
--
--   **Theorem.** Let $B$ assign to every word $a$ a rational number $B(a)$ such that $B(a)\ge0$ and $\|\partial^a u(z)\|_\infty\le B(a)$ for every word $a$ and every $z\in\mathbb{R}\times\mathbb{R}^3$. Put $L_B(a)=\sum_{j=0}^{3}B(ja)$. Then for every word $a$ and all $z,w\in\mathbb{R}\times\mathbb{R}^3$,
--
--   $$
--   \big\|\partial^a u(z)-\partial^a u(w)\big\|_\infty\le L_B(a)\,\|z-w\|.
--   $$
--
--   In words: uniform bounds on all derivatives one order higher give an explicit global Lipschitz constant for each mixed derivative. When $a\mapsto B(a)$ is computable, so is $a\mapsto L_B(a)$, and the estimate controls the error made when a derivative at a real point $z$ is replaced by its value at a nearby rational point. This is how procedures that evaluate derivatives at rational points are upgraded to procedures that work from approximations of arbitrary points.
--
--   **Formalization Note** Words are lists `a : List (Fin 4)`; the mixed derivative is `mixedDerivative u a`, defined with `fderiv` along `spacetimeBasis j`; and `Smooth u` means `ContDiff ℝ ⊤` for the uncurried map on `SpaceTime = ℝ × (Fin 3 → ℝ)`. The bound is a function `B : List (Fin 4) → ℚ` cast to the reals, and the constant is `jetLipschitz B a`. Nonnegativity of `B` is a separate hypothesis, although it also follows from the derivative bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean#L318-L343

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms

open OAI OAI.Solenoidal
open Set Filter Encodable
open scoped BigOperators Topology

theorem OAI.Solenoidal.mixed_lipschitz {u : Field} (hu : Smooth u) {B : List (Fin 4) → ℚ}
    (hB : ∀ a, 0 ≤ B a) (hb : ∀ a z, ‖mixedDerivative u a z‖ ≤ (B a:ℝ))
    (a : List (Fin 4)) (z w : SpaceTime) :
    ‖mixedDerivative u a z - mixedDerivative u a w‖ ≤ (jetLipschitz B a:ℝ)*‖z-w‖ := by sorry
