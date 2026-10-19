-- Prove2me | Theorems.Thm_OAI_C0Absorption_RadiusLocalization_low_bands_disjoint
-- name    : OAI.C0Absorption.RadiusLocalization.low_bands_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:18:49.580954+00:00
-- url     : https://prove2.me/theorems/c877a10c-781f-4e34-a48f-0660487e91c2
-- title:
--   Detectors with a fixed band and distinct indices can be disjointified
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ is detected by tests $F_i$ if $|\langle F_i,m_i\rangle|\ge\delta>0$; the goal is to make the detecting tests compatible, i.e. all signed sums $\sum\pm F_i$ uniformly Lipschitz. Let a radius localization be given, and let $V$-tests with distinct indices $\gamma_i$, all of the same band $j\le h$ and complexity at most $h$, detect $(m_i)$ with constant $\delta$. Then there are $H$, a subsequence and tests $F_i\in V_H$ with pairwise disjoint supports and
--   $$
--   |\langle F_i,m_{\varphi(i)}\rangle|\ge\delta/2 .
--   $$
--
--   Distinct cylinder indices of a fixed band eventually see disjoint tail regions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Supports.lean#L148-L179

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

open OAI OAI.C0Absorption OAI.C0Absorption.RadiusLocalization
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

include loc in
theorem OAI.C0Absorption.RadiusLocalization.low_bands_disjoint (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h j : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i)=j) (hjh : j ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (hγ : Function.Injective γ) (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      Pairwise (fun i k => Disjoint (tsupport (F i)) (tsupport (F k))) := by sorry
