-- Prove2me | Theorems.Thm_OAI_Solenoidal_Computing_rat_inv
-- name    : OAI.Solenoidal.Computing.rat_inv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:07.020984+00:00
-- url     : https://prove2.me/theorems/fabce0ca-e620-4b0a-bf27-9f37accbd27b
-- title:
--   Inversion of rational numbers is primitive recursive
-- statement:
--   Primitive recursion is taken in the sense of encodable types: a function between types with fixed encodings into $\mathbb{N}$ is *primitive recursive* if, read through the encodings, it becomes a primitive recursive function on natural numbers (Mathlib's notion `Primrec`). A rational number $q$ is encoded through its reduced representation $q=a/b$ with $a\in\mathbb{Z}$, $b\in\mathbb{N}$, $b>0$ and $\gcd(|a|,b)=1$, i.e. through the pair $(a,b)$, which gives the same codes as Mathlib's standard encoding of $\mathbb{Q}$.
--
--   **Theorem.** The map
--
--   $$
--   \mathbb{Q}\to\mathbb{Q},\qquad q\mapsto q^{-1}\quad(\text{with } 0^{-1}=0),
--   $$
--
--   is primitive recursive.
--
--   This completes the field operations on $\mathbb{Q}$ needed for the rational interval arithmetic (for instance the clamped inversion of rational balls) by which the forcing field and its derivatives are approximated by one fixed algorithm.
--
--   **Formalization Note** The statement is `Primrec (fun q : ℚ => q⁻¹)`; in Lean the inverse of $0$ is $0$. The `Primcodable ℚ` instance is constructed in the same file by transporting the subtype of reduced pairs (positive denominator, coprime to the numerator) along the bijection $q\mapsto(\mathrm{num}\,q,\mathrm{den}\,q)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean#L236-L248

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

open OAI OAI.Solenoidal OAI.Solenoidal.Computing
open Encodable

theorem OAI.Solenoidal.Computing.rat_inv : Primrec (fun q : ℚ => q⁻¹) := by sorry
