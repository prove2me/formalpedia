-- Prove2me | Theorems.Thm_OAI_C0Absorption_high_bands_compatible
-- name    : OAI.C0Absorption.high_bands_compatible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:15:31.170367+00:00
-- url     : https://prove2.me/theorems/a8de5394-91d5-445c-82cf-fde63fa401c2
-- title:
--   Detectors with growing bands can be made compatible
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ is detected by tests $F_i$ if $|\langle F_i,m_i\rangle|\ge\delta>0$; the goal is to make the detecting tests compatible, i.e. all signed sums $\sum\pm F_i$ uniformly Lipschitz. Let a tag localization be given, and let $T$-tests $r_i.\mathrm{value}$, with at most $h$ operations and bands tending to infinity, detect $(m_i)$ with constant $\delta$. Then there are a subsequence and tests $F_i\in T_{h+1}$ with
--   $$
--   |\langle F_i,m_{\varphi(i)}\rangle|\ge\delta/2,\qquad\sum_{i<n}\pm F_i\ \text{is}\ (4^{h+1}L_0+1)\text{-Lipschitz}.
--   $$
--
--   High bands localize the tests in ever smaller cylinders, which forces compatibility.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Selection.lean#L211-L258

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
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.high_bands_compatible {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i)) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h)
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ TClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+1) (fun s => ∑ i, ε i*F i s) := by sorry
