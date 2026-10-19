-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_rounding_obstruction
-- name    : OAI.GrahamSpherical.rounding_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:09:40.153884+00:00
-- url     : https://prove2.me/theorems/9aaf86bb-2832-4a24-82ce-827d31cef985
-- title:
--   Twelve reals with weighted sum $8$ cannot share a residue of $\lfloor3e\rfloor$ modulo $50$
-- statement:
--   Let $e_{k,q}\in\mathbb{R}$ for $(k,q)\in\{0,1,2\}\times\{0,1,2,3\}$ satisfy
--   $$
--   \sum_{q}\bigl(e_{0,q}+e_{1,q}-2e_{2,q}\bigr)=8 .
--   $$
--   Then there are labels $i,j$ with $\lfloor3e_i\rfloor\not\equiv\lfloor3e_j\rfloor\pmod{50}$.
--
--   No sign condition on the $e_i$ is needed. Applied to the derivation energies of an isometric copy of the witness, it shows that the copy is not monochromatic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/Coloring.lean#L17-L75

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model

open OAI OAI.GrahamSpherical
open scoped BigOperators

theorem OAI.GrahamSpherical.rounding_obstruction (e : (Fin 3 × Fin 4) → ℝ)
    (henergy : ∑ i, (if i.1 = 2 then (-2 : ℝ) else 1) * e i = 8) :
    ∃ i j, (Int.floor (3 * e i)) % 50 ≠ (Int.floor (3 * e j)) % 50 := by sorry
