-- Prove2me | Theorems.Thm_OAI_Solenoidal_Computing_int_mul
-- name    : OAI.Solenoidal.Computing.int_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:52:29.4635+00:00
-- url     : https://prove2.me/theorems/aa4fa1da-011b-46a6-a272-35c2aa0b05fb
-- title:
--   Integer multiplication is primitive recursive
-- statement:
--   Primitive recursion is taken in the sense of encodable types: each type carries a fixed encoding into $\mathbb{N}$, and a function between such types is *primitive recursive* if, read through the encodings, it becomes a primitive recursive function on natural numbers (Mathlib's notion `Primrec`; a two-argument function is primitive recursive if it is so as a function on pairs). Integers are encoded by $n\mapsto2n$ for $n\ge0$ and $-(n+1)\mapsto2n+1$.
--
--   **Theorem.** Multiplication of integers,
--
--   $$
--   \mathbb{Z}\times\mathbb{Z}\to\mathbb{Z},\qquad (a,b)\mapsto a\,b,
--   $$
--
--   is primitive recursive.
--
--   Together with primitive recursiveness of integer addition and negation this yields primitive recursive arithmetic on rational numbers, which is needed to show that the rational approximation procedures for the forcing field are given by a single fixed algorithm.
--
--   **Formalization Note** The statement is `Primrec₂ ((·*·) : ℤ → ℤ → ℤ)` for Mathlib's `Primcodable ℤ` instance; integers are handled through the constructors `Int.ofNat n` and `Int.negSucc n` $=-(n+1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Computing.lean#L105-L122

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

theorem OAI.Solenoidal.Computing.int_mul : Primrec₂ ((·*·) : ℤ → ℤ → ℤ) := by sorry
