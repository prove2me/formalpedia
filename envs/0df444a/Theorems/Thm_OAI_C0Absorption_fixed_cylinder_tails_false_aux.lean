-- Prove2me | Theorems.Thm_OAI_C0Absorption_fixed_cylinder_tails_false_aux
-- name    : OAI.C0Absorption.fixed_cylinder_tails_false_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:22:03.389434+00:00
-- url     : https://prove2.me/theorems/6d4c57e4-05b8-41d2-a589-15cfa491b7ce
-- title:
--   A fixed generated test with varying tail factors cannot detect a c0 sequence
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ has bounded signed sums if $\|\sum_{i\in F}\pm m_i\|\le M$ for every finite set $F$ of distinct indices and every choice of signs. Fix a generated representation $r$ for an index of band at most $h$, with at most $h$ operations. Let tail lists $\mathrm{pre}\,\cdot\,\mathrm{post}_i$ of total length at most $h$ and scale indices at most $h$ have varying parts $\mathrm{post}_i$ of fixed length $n$. Then it is impossible that
--   $$
--   \Bigl|\Bigl\langle r\cdot\prod_{t\in\mathrm{pre}\,\mathrm{post}_i}t,\;m_i\Bigr\rangle\Bigr|\ge\delta>0\quad\text{for all }i .
--   $$
--
--   This is proved by induction on $n$, for every prefix simultaneously.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Detection.lean#L36-L128

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

theorem OAI.C0Absorption.fixed_cylinder_tails_false_aux {γ : Γ} (r : GeneratedRepresentation B γ) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List TailOperation) (post : ℕ → List TailOperation),
      (∀ i, (post i).length=n) →
      (∀ i, (pre++post i).length ≤ h) →
      (∀ i t, t ∈ pre++post i → t.scaleIndex ≤ h) →
      ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
      ∀ δ : ℝ, 0 < δ →
      (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
        (fun s => r.value s*tailProduct (pre++post i) s) (m i)|) → False := by sorry
