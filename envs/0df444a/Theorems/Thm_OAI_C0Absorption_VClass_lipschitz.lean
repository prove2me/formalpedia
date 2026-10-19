-- Prove2me | Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
-- name    : OAI.C0Absorption.VClass_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:08:11.512127+00:00
-- url     : https://prove2.me/theorems/6d387a35-9eb7-41a7-aed5-6ce678498acb
-- title:
--   Lipschitz bound for the V test classes
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. Every $f\in V_h$ is Lipschitz on $B$ with constant
--   $$
--   4^hL_0+h\,4^hA,
--   $$
--   where $L_0$ and $A$ are the Lipschitz constant and sup bound of the base functions.
--
--   Tests in a fixed class are uniformly Lipschitz, hence uniformly bounded functionals on the source space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Tests.lean#L242-L255

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.VClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by sorry
