-- Prove2me | Theorems.Thm_OAI_C0Absorption_GeneratedRepresentation_exists_flatten_T
-- name    : OAI.C0Absorption.GeneratedRepresentation.exists_flatten_T
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:12:58.18581+00:00
-- url     : https://prove2.me/theorems/7760f027-e459-449c-8099-810ba0fff123
-- title:
--   Appending a fine flattening barely changes a T-test pairing
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. Let $r$ be a generated representation with at most $h$ operations, $v$ a cube point, $z\in Z_{\mathrm{src}}$, and $\delta,\mathrm{cap}>0$. Then there is a scale index $a$ with $2^{-a}<\mathrm{cap}$ such that appending the flattening at scale $2^{-a}$ near $v$ gives $r'$ with
--   $$
--   \bigl|\langle r'.\mathrm{value},z\rangle-\langle r.\mathrm{value},z\rangle\bigr|<\delta .
--   $$
--   Moreover $r'$ is constant near $v$ (within $\frac38\cdot2^{-a}$) and bounded by $2^{|r|}A$.
--
--   This is the version without tail factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Duality.lean#L252-L299

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality

open OAI OAI.C0Absorption OAI.C0Absorption.GeneratedRepresentation
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem OAI.C0Absorption.GeneratedRepresentation.exists_flatten_T (r : GeneratedRepresentation B γ)
    (h : ℕ) (hr : r.operations.length ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin r'.value z-
        completedPairing (sourceClasses B) c0Origin r.value z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by sorry
