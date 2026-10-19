-- Prove2me | Theorems.Thm_MIPRE_LCS_isMeasurementSystem_observableToProjector
-- name    : MIPRE.LCS.isMeasurementSystem_observableToProjector
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:03.335118+00:00
-- url     : https://prove2.me/theorems/9f2d0da2-151d-4852-85a6-3414b2f2ef8a
-- title:
--   Given an observable $O$, the mapping observableToProjector O is a measurement system
-- statement:
--   A statement of the module `MIPRE.LCS.Strategy.ObservableToProjector` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Conversion from Observables to Projectors. This module defines the mapping from observables (self-adjoint involutive operators) to projector measurement systems and proves their fundamental algebraic properties. Given an observable $O$, we define two projectors $P_0, P_1$ corresponding to the outcomes $\{0, 1\} \subseteq \mathbb{F}_2$: - $P_0 = \frac{1}{2}(I + O)$ - $P_1 = \frac{1}{2}(I - O)$ These projectors form a complete binary measurement system.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   Given an observable $O$, the mapping `observableToProjector O` is a measurement system.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LCS
--   variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
--
--   theorem MIPRE.LCS.isMeasurementSystem_observableToProjector (O : R) (hO : IsObservable O) :
--       IsMeasurementSystem (observableToProjector O)
--   ```
--
--   **Formalization Note** `MIPRE.LCS.isMeasurementSystem_observableToProjector` is declared in `MIPRE/LCS/Strategy/ObservableToProjector.lean`, lines 140–153. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Strategy/ObservableToProjector.lean#L140-L153; blueprint lem:observable-projector

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector

open MIPRE
open MIPRE.LCS
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

theorem MIPRE.LCS.isMeasurementSystem_observableToProjector (O : R) (hO : IsObservable O) :
    IsMeasurementSystem (observableToProjector O) := by sorry
