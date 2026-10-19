-- Prove2me | Theorems.Thm_OAI_C0Absorption_small_remainders_false
-- name    : OAI.C0Absorption.small_remainders_false
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:21:01.611364+00:00
-- url     : https://prove2.me/theorems/738b8f24-3af1-4a30-92cb-6fe4d098d330
-- title:
--   Detectors through shrinking remainder operations cannot see a c0 sequence
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ has bounded signed sums if $\|\sum_{i\in F}\pm m_i\|\le M$ for every finite set $F$ of distinct indices and every choice of signs. Fix an index $\gamma$ with band at most $h$. Suppose each detector $r_i\cdot(\text{tails }t_i)$, with at most $h$ operations and $h$ tail factors, has cube value $\mathrm{suf}_i(R_{q_i,\rho_i}p)$: a remainder operation at scale $\rho_i\to0$ applied to a fixed $K$-Lipschitz function $p$, followed by at most $h$ operations of scale at most $\rho_i$. Then it is impossible that
--   $$
--   \bigl|\langle r_i\cdot t_i,m_i\rangle\bigr|\ge\delta>0\quad\text{for all }i .
--   $$
--
--   Detectors that vanish in the limit cannot uniformly detect a sequence with bounded signed sums.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Operations.lean#L223-L268

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.small_remainders_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (op : ℕ → CylinderOperation (B.coordinates γ))
    (hsmall : Tendsto (fun i => (op i).scale) atTop (nhds 0))
    (p : Cube (B.coordinates γ) → ℝ) (K : ℝ≥0) (hp : LipschitzWith K p)
    (suf : ℕ → List (CylinderOperation (B.coordinates γ)))
    (hlen : ∀ i, (suf i).length ≤ h)
    (horder : ∀ i t, t ∈ suf i → t.scale ≤ (op i).scale)
    (heq : ∀ i, (r i).cubeValue = applyOperations (suf i) ((op i).remainder.act p))
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by sorry
