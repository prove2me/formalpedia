-- Prove2me | Theorems.Thm_OAI_Solenoidal_norm_flatten
-- name    : OAI.Solenoidal.norm_flatten
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:54:56.22715+00:00
-- url     : https://prove2.me/theorems/134b3427-b22b-4168-b965-c063ebe125d9
-- title:
--   The max norm of a space-time point equals the sup norm of its four coordinates
-- statement:
--   Write points of space-time $\mathbb{R}\times\mathbb{R}^3$ as $z=(t,x)$ with time $t\in\mathbb{R}$ and position $x=(x_0,x_1,x_2)\in\mathbb{R}^3$. Position space carries the maximum norm $\|x\|_\infty=\max_{0\le i\le 2}|x_i|$, and space-time carries the product norm $\|(t,x)\|=\max\big(|t|,\|x\|_\infty\big)$. Let $\operatorname{flat}(z)=(t,x_0,x_1,x_2)\in\mathbb{R}^4$ be the vector of the four coordinates of $z$, measured in the maximum norm of $\mathbb{R}^4$.
--
--   **Theorem.** For every $z=(t,x)\in\mathbb{R}\times\mathbb{R}^3$,
--
--   $$
--   \|\operatorname{flat}(z)\|_\infty=\max\big(|t|,|x_0|,|x_1|,|x_2|\big)=\max\big(|t|,\|x\|_\infty\big)=\|z\|.
--   $$
--
--   Thus $\operatorname{flat}$ identifies $\mathbb{R}\times\mathbb{R}^3$ isometrically with $\mathbb{R}^4$ for these norms. The identity lets one pass between estimates on coordinate vectors and estimates on space-time points: a rational approximation of the four coordinates of a point to within $2^{-n}$ is a space-time approximation to within $2^{-n}$, and each coordinate of a direction vector $v$ is bounded in absolute value by $\|v\|$ when a directional derivative is expanded in the coordinate basis.
--
--   **Formalization Note** Space-time is `SpaceTime = ℝ × (Fin 3 → ℝ)` and `flatten z = ![z.1, z.2 0, z.2 1, z.2 2] : Fin 4 → ℝ`. The norms are Mathlib's default ones: the sup norm on `Fin n → ℝ` and the maximum of the two component norms on a product.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean#L287-L303

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

theorem OAI.Solenoidal.norm_flatten (z : SpaceTime) : ‖flatten z‖ = ‖z‖ := by sorry
