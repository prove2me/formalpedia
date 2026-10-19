-- Prove2me | Theorems.Thm_OAI_C0Absorption_tail_separation
-- name    : OAI.C0Absorption.tail_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:18:13.486518+00:00
-- url     : https://prove2.me/theorems/cc95c458-3b6b-4f02-941a-1d0bce97515f
-- title:
--   Separating detectors living on large tails
-- statement:
--   Let $Z_{\mathrm{src}}$ be the source space built from cylinder bases on the unit ball $B$ of $c_0$. Its test classes are $T_h$ (generated representations with at most $h$ flattening or remainder operations) and $V_h$ (such values times at most $h$ tail factors), and $\langle f,z\rangle$ is the extended pairing of a bounded test $f$ with $z\in Z_{\mathrm{src}}$. A sequence $(m_i)$ in $Z_{\mathrm{src}}$ is detected by tests $F_i$ if $|\langle F_i,m_i\rangle|\ge\delta>0$; the goal is to make the detecting tests compatible, i.e. all signed sums $\sum\pm F_i$ uniformly Lipschitz. Let $F_i\in V_h$ detect $(m_i)$ with constant $\delta$. Suppose there are $c_*>0$ and $M_i\to\infty$ with $\tau_{M_i}(s)\ge c_*$ on the support of $F_i$, where $\tau_N(s)=\sup_{k>N}|s_k|$. Then there are $H$, a subsequence and tests $G_i\in V_H$ with
--   $$
--   |\langle G_i,m_{\varphi(i)}\rangle|\ge\delta/2\quad\text{and}\quad\operatorname{supp}G_i\cap\operatorname{supp}G_k=\emptyset\ (i\ne k).
--   $$
--
--   Tests seeing large tails can be cut off by tail factors into disjointly supported tests.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Supports.lean#L33-L89

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
variable {Γ : Type*} {B : CylinderBases Γ}

theorem OAI.C0Absorption.tail_separation {h : ℕ} (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (hF : ∀ i, F i ∈ VClass B h) {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hdetect : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hsupport : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (M i) s.val) :
    ∃ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℕ → C0Ball → ℝ,
      (∀ i, G i ∈ VClass B H) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (G i) (m (φ i))|) ∧
      Pairwise (fun i j => Disjoint (tsupport (G i)) (tsupport (G j))) := by sorry
