-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_lemma_A_3
-- name    : LogSupermodularBIS.Main.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:35.796704+00:00
-- url     : https://prove2.me/theorems/83fdc7ba-5f8a-46b3-babd-ed2c624066ff
-- title:
--   Lemma A.3 — Sinclair–Jerrum walk: reversibility, leaf and root mass, conditional leaf law and mixing
-- statement:
--   Let a finite rooted tree have all its leaves at depth $d\ge1$, and let every leaf $x$ carry a weight $\omega_x>0$. Let $Z_v$ be the sum of the weights of the leaves below $v$, and let the estimates satisfy $Z_v/\mathcal B\le q_v\le Z_v$ at every node and $q_x=\omega_x$ at every leaf, for a distortion $\mathcal B\ge1$. Put $h_0=2\mathcal Bd$, $\Gamma=32\mathcal B^4d^2$, and let $L$ be the set of leaves. Then the walk $P_{tr}$ is reversible with stationary law $\pi(v)=s_v/S_o$:
--   $$\pi(v)P_{tr}(v,y)=\pi(y)P_{tr}(y,v),\qquad \sum_v\pi(v)P_{tr}(v,y)=\pi(y),\qquad\sum_v\pi(v)=1;$$
--   moreover $\pi(L)\ge1/h_0$, $\pi(o)\ge1/(h_0\mathcal B)$, $\pi(x\mid L)=\omega_x/Z_o$ at every leaf $x$, and for $0<\eta_0<1$,
--   $$\|P_{tr}^t(o,\cdot)-\pi\|_{TV}\le\eta_0\quad\text{whenever}\quad t\ge\Gamma\log\frac{h_0\mathcal B}{\eta_0}.\tag{A.3}$$
--
--   This is the weighted, superpolynomial-distortion form of the Sinclair–Jerrum bounds used to convert coarse estimates into samples.
--
--   **Formalization Note.** $t$ ranges over the natural numbers and $P_{tr}^t$ is the $t$-th matrix power.
--
--   Differences from the source:
--   - encoding: reversible with stationary law π → detailed balance, stationarity and normalization of π, stated separately; reason: spells out the three properties of a reversible stationary law
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 40 (PDF 41), Lemma A.3, (A.3)

import Definitions.Def_LogSupermodularBIS_Main_TreeWalk
import Definitions.Def_LogSupermodularBIS_Main_Machine

open MeasureTheory

set_option autoImplicit false

open HarelTarjan.Compressed

namespace LogSupermodularBIS.Main

/-- Lemma A.3 (Sinclair–Jerrum walk), p. 40. -/
theorem lemma_A_3 {V : Type*} [Fintype V] [DecidableEq V] (𝒯 : RootedTree V) (d : ℕ)
    (hd : 1 ≤ d) (hleaf : ∀ x, TreeWalk.IsLeaf 𝒯 x → depth 𝒯 x = d)
    (ω q : V → ℝ) (hω : ∀ x, TreeWalk.IsLeaf 𝒯 x → 0 < ω x) (ℬ : ℝ) (hℬ : 1 ≤ ℬ)
    (hq : ∀ v, TreeWalk.mass 𝒯 ω v / ℬ ≤ q v ∧ q v ≤ TreeWalk.mass 𝒯 ω v)
    (hqleaf : ∀ x, TreeWalk.IsLeaf 𝒯 x → q x = ω x) :
    let P := TreeWalk.walk 𝒯 q
    let π := TreeWalk.stationaryLaw 𝒯 q
    let h₀ : ℝ := 2 * ℬ * d
    let Γ : ℝ := 32 * ℬ ^ 4 * (d : ℝ) ^ 2
    let πL : ℝ := ∑ x, (open Classical in if TreeWalk.IsLeaf 𝒯 x then π x else 0)
    (∀ v y, π v * P v y = π y * P y v) ∧
    (∀ y, ∑ v, π v * P v y = π y) ∧
    (∑ v, π v = 1) ∧
    1 / h₀ ≤ πL ∧
    1 / (h₀ * ℬ) ≤ π 𝒯.root ∧
    (∀ x, TreeWalk.IsLeaf 𝒯 x → π x / πL = ω x / TreeWalk.mass 𝒯 ω 𝒯.root) ∧
    ∀ η₀ ∈ Set.Ioo (0 : ℝ) 1, ∀ t : ℕ, Γ * Real.log (h₀ * ℬ / η₀) ≤ t →
      tvDist (fun v => (P ^ t) 𝒯.root v) π ≤ η₀ := by sorry

end LogSupermodularBIS.Main
