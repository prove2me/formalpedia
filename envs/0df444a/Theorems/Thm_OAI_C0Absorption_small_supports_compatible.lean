-- Prove2me | Theorems.Thm_OAI_C0Absorption_small_supports_compatible
-- name    : OAI.C0Absorption.small_supports_compatible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:19:30.974025+00:00
-- url     : https://prove2.me/theorems/8fba7b89-7ddc-4c13-937c-c2f92770ab7c
-- title:
--   Detectors with shrinking supports and values can be made compatible
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ is detected by tests $F_i$ if $|\langle F_i,m_i\rangle|\ge\delta>0$; the goal is to make the detecting tests compatible, i.e. all signed sums $\sum\pm F_i$ uniformly Lipschitz. Fix an index $\gamma$ with band at most $h$. Let representations $r_i$ with at most $h$ operations, times at most $h$ tail factors, detect $(m_i)$ with constant $\delta$. Suppose the cube values satisfy $|r_i.\mathrm{cubeValue}|\le b_i$ with $b_i\to0$ and are supported within $a_i\to0$ of points $q_i$. Then there are a subsequence and tests $F_i\in V_{h+1}$ with $|\langle F_i,m_{\varphi(i)}\rangle|\ge\delta/2$ and all signed sums
--   $$
--   \sum_{i<n}\pm F_i\quad(4^{h+1}L_0+(h+1)4^{h+1}A+1)\text{-Lipschitz}.
--   $$
--
--   Shrinking bumps of one index can be nested into a compatible family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Supports.lean#L190-L265

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.small_supports_compatible {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (q : ℕ → Cube (B.coordinates γ)) (a b : ℕ → ℝ)
    (haPos : ∀ i, 0 < a i) (ha0 : Tendsto a atTop (nhds 0)) (hb0 : Tendsto b atTop (nhds 0))
    (hsup : ∀ i x, |(r i).cubeValue x| ≤ b i)
    (hsupp : ∀ i x, x ∈ tsupport (r i).cubeValue → dist x (q i) ≤ a i)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A+1)
          (fun s => ∑ i, ε i*F i s) := by sorry
