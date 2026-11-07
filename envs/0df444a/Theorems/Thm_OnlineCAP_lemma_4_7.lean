-- Prove2me | Theorems.Thm_OnlineCAP_lemma_4_7
-- name    : OnlineCAP.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:06.939463+00:00
-- url     : https://prove2.me/theorems/d625384c-2968-4a54-ae5f-9db03eee3561
-- title:
--   Lemma 4.7 — the candidate queries have O(log n · |W| · κ²) shallow traces
-- statement:
--   There is a constant $C$ such that for every finite point set $P\subseteq\mathbb R^2$ with $n=|P|\ge2$, every assignment of activation times $\tau_e\in\mathbb N$ to the virtual points $\mathcal P=P\times[n]$, every $W\subseteq\mathcal P$ and every integer $\kappa\ge1$,
--   $$\big|\{Q\cap W : Q\in\mathcal F,\ 1\le|Q\cap W|\le\kappa\}\big|\le C\cdot\log n\cdot|W|\cdot\kappa^2 ,\tag{4}$$
--   where $\mathcal F$ is the family of all candidate query sets $T_{\mathrm{leaf}},T_{\mathrm{left}},T_{\mathrm{right}}$ generated at the nodes of the range tree (for all parameters).
--
--   This is the shallow-cell-complexity bound $\varphi(m,\kappa)=O(\log n)\,\kappa^2$ that lets Algorithm 2 use the sampler of Lemma 4.4.
--
--   Differences from the source:
--   - generalization: the activation times τ_e of a run of Algorithm 2 (Definition 4.6) → an arbitrary function τ : 𝒫 → ℕ; reason: covers every run
--   - reading: the family of all candidate query sets Q_t that can be generated across all nodes of the range tree → the union over nodes of the octant families T_leaf, T_left, T_right of the proof (p.19), over all a, b, c ∈ ℝ and t ∈ ℕ; reason: this is the family the proof bounds, and it contains every query the algorithm can send; the larger family gives the stronger bound
--   - encoding: a balanced binary range tree on the x-coordinates → the dyadic tree on x-ranks, nodes (h, j) with h ≤ ⌈log₂ m⌉; reason: a balanced binary tree of height O(log n) in which every point lies in at most ⌈log₂ m⌉ + 1 nodes, the property the proof uses
--   - encoding: ≤ O(log n · |W| · κ²) → ≤ C · log n · |W| · κ² for n ≥ 2; reason: one constant for all instances; log 1 = 0 makes the bound meaningless at n = 1
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Lemma 4.7, p.18 (proof pp.19–20)

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_HasSCC
import Definitions.Def_OnlineCAP_xrank
import Definitions.Def_OnlineCAP_IsNode
import Definitions.Def_OnlineCAP_nodeSet
import Definitions.Def_OnlineCAP_candFamily

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Lemma 4.7 (Shallow traces).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Lemma 4.7, p.18 (PDF p.18): "Let F denote the family of
all candidate query sets Qt ⊆ 𝒫 that can be generated across all nodes of the range tree. For any
subset W ⊆ 𝒫 and integer κ ≥ 1, |{Qt ∩ W : Qt ∈ F and 1 ≤ |Qt ∩ W| ≤ κ}| ≤ O(log n · |W| · κ²). (4)"

There is a constant `C` such that for every point set `P ⊆ ℝ²` with `n = |P| ≥ 2`, every
assignment of activation times `τ` to the virtual points `𝒫 = P × [n]`, every `W ⊆ 𝒫` and every
integer `κ ≥ 1`, the number of distinct traces `Q ∩ W`, `Q ∈ F`, with `1 ≤ |Q ∩ W| ≤ κ`, is at most
`C · log n · |W| · κ²`.

**Formalization Note.** `F = candFamily P τ` is the union over the nodes of the range tree of the
octant families `T_left`, `T_right` (internal nodes) and `T_leaf` (leaves) of the proof (p.19), for
all parameters; it contains every query Algorithm 2 sends when `τ` are its activation times
(Definition 4.6). Traces are counted as sets of virtual points. `n ≥ 2` because `log 1 = 0`. -/
theorem lemma_4_7 : ∃ C : ℝ, ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card → ∀ (τ : VirtualPt P → ℕ)
    (W : Finset (VirtualPt P)) (κ : ℕ), 1 ≤ κ →
    ((shallowTraces (candFamily P τ) W κ).card : ℝ) ≤
      C * Real.log P.card * W.card * (κ : ℝ) ^ 2 := by sorry

end OnlineCAP
