-- Prove2me | Theorems.Thm_OAI_C0Absorption_source_noLinearC0
-- name    : OAI.C0Absorption.source_noLinearC0
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:24:41.626129+00:00
-- url     : https://prove2.me/theorems/f2f24abf-085c-4a30-b2a4-81cc87e9b290
-- title:
--   The source space contains no linear copy of c0
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. Assume tag localization and radius localization for the cylinder bases. Then there is no bounded linear map $T:c_0\to Z_{\mathrm{src}}$ and constant $c>0$ with
--   $$
--   \|Tx\|\ge c\|x\|\qquad(x\in c_0).
--   $$
--
--   So $Z_{\mathrm{src}}$ has no subspace isomorphic to $c_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Detection.lean#L372-L386

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
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

theorem OAI.C0Absorption.source_noLinearC0 (locT : TagLocalization B) (locR : RadiusLocalization B) :
    NoLinearC0 (SourceSpace B) := by sorry
