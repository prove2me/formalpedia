-- Prove2me | Theorems.Thm_OAI_C0Absorption_repeated_label_false_aux
-- name    : OAI.C0Absorption.repeated_label_false_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:23:12.081556+00:00
-- url     : https://prove2.me/theorems/a1dd834e-a02f-4b23-b4e4-5f6513f67c20
-- title:
--   Detectors at one repeated index cannot see a c0 sequence
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ has bounded signed sums if $\|\sum_{i\in F}\pm m_i\|\le M$ for every finite set $F$ of distinct indices and every choice of signs. Fix an index $\gamma$ of band at most $h$. Let generated representations $r_i$ for $\gamma$ have operation lists $\mathrm{pre}\,\cdot\,\mathrm{post}_i$ with varying parts of fixed length $n$, at most $h$ operations in total, and tail lists $t_i$ of length and scale indices at most $h$. Then it is impossible that
--   $$
--   \bigl|\langle r_i\cdot t_i,m_i\rangle\bigr|\ge\delta>0\quad\text{for all }i .
--   $$
--
--   This is proved by induction on the number $n$ of varying operations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Detection.lean#L162-L258

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
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem OAI.C0Absorption.repeated_label_false_aux (h : ℕ) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List (CylinderOperation (B.coordinates γ)))
      (post : ℕ → List (CylinderOperation (B.coordinates γ)))
      (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation),
    (∀ i, (post i).length=n) → (∀ i, (r i).operations=pre++post i) →
    (∀ i, (r i).operations.length ≤ h) →
    (∀ i, (ts i).length ≤ h) → (∀ i t, t ∈ ts i → t.scaleIndex ≤ h) →
    ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
    ∀ δ : ℝ, 0<δ →
    (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) → False := by sorry
