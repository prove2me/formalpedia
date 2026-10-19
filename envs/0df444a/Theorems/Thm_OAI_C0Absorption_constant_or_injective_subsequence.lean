-- Prove2me | Theorems.Thm_OAI_C0Absorption_constant_or_injective_subsequence
-- name    : OAI.C0Absorption.constant_or_injective_subsequence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:13:32.198088+00:00
-- url     : https://prove2.me/theorems/d8fa05ba-0bff-43e9-a55d-8ab09fc88cb5
-- title:
--   Every sequence has a constant or an injective subsequence
-- statement:
--   For every sequence $f:\mathbb N\to A$ in an arbitrary type, either some value is taken along a subsequence,
--   $$
--   \exists a,\ \exists\varphi\ \text{strictly increasing}:\ f(\varphi(i))=a\ \text{for all }i,
--   $$
--   or there is a strictly increasing $\varphi$ with $f\circ\varphi$ injective.
--
--   This infinite pigeonhole principle splits the analysis of detecting tests into the case of one fixed index and the case of distinct indices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Selection.lean#L33-L47

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology

theorem OAI.C0Absorption.constant_or_injective_subsequence {A : Type*} (f : ℕ → A) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (f ∘ φ)) := by sorry
