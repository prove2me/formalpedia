-- Prove2me | Theorems.Thm_IDEPoA_lemma_3_8
-- name    : IDEPoA.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:41.902351+00:00
-- url     : https://prove2.me/theorems/9db94c76-c7a9-4e58-b84c-dc8fc82082b7
-- title:
--   Lemma 3.8: a sink-like subgraph extends by the closest outside node (corrected: $t\in T$)
-- statement:
--   Let $f$ be an IDE flow. Let $T$ be a node set, $v\notin T$ a closest node to $t$ outside $T$ with respect to physical distance, and $T'=T\cup\{v\}$. Let
--   $$\theta_2\ge\theta_1+\sum_{e\in E\setminus E(T)}\Bigl(\tau_e+\frac1{2\nu_e}\Bigr),\qquad\theta_2'=\theta_2-\sum_{e\in E(T')\setminus E(T)}\Bigl(\tau_e+\frac1{2\nu_e}\Bigr).$$
--   If $T$ is sink-like on $[\theta_1,\theta_2]$, then $T'$ is sink-like on $[\theta_1,\theta_2']$.
--
--   For equality in the bound on $\theta_2$, this is the printed lemma, with $\theta_2'=\theta_1+\sum_{e\in E\setminus E(T')}(\tau_e+\frac1{2\nu_e})$. Iterating it from $T=\{t\}$ grows a sink-like subgraph to the whole graph, at the price of a shorter interval.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - correction: T any induced subgraph with the two properties of Definition 3.5 → t ∈ T as part of being sink-like; reason: T = ∅ breaks the printed lemma: on one edge st with τ = ν = 1, inflow 1 on [0,1), θ0 = 1, θ1 = 1, θ2 = θ2′ = 5/2, the empty subgraph is sink-like, the closest node is t, and vol of {t} is 1
--   - generalization: θ2 := θ1 + ∑ over E∖E(T) and θ2′ := θ1 + ∑ over E∖E(T′) → every θ2 at least θ1 + ∑ over E∖E(T), with θ2′ := θ2 − ∑ over E(T′)∖E(T); reason: equality is the printed lemma; the interval conclusion of Claim 5 needs the slack
--   - reading: flow f left implicit → f an IDE flow; reason: Claim 3 uses (7)
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 3.8, p.18

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 3.8 (Graf & Harks, arXiv:2007.07794v2, p.18), with slack: let `f` be an IDE flow, `v` a
closest node to `t` outside `T`, `T' = T ∪ {v}`, and `θ₂ ≥ θ₁ + ∑_{e ∉ E(T)} (τₑ + 1/(2νₑ))`. If `T`
is sink-like on `[θ₁, θ₂]`, then `T'` is sink-like on `[θ₁, θ₂']` with
`θ₂' = θ₂ − ∑_{e ∈ E(T') ∖ E(T)} (τₑ + 1/(2νₑ))`.

For `θ₂ = θ₁ + ∑_{e ∉ E(T)} (τₑ + 1/(2νₑ))` this is the printed lemma, since then
`θ₂' = θ₁ + ∑_{e ∉ E(T')} (τₑ + 1/(2νₑ))`. The slack is what the interval conclusion of Claim 5
needs. The sink belongs to `T` by `IsSinkLike` (corrected Definition 3.5). -/
theorem lemma_3_8 [DecidableEq E] (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsIDE N f)
    (T : Finset V) (v : V) (hv : v ∉ T) (hclosest : ∀ w, w ∉ T → physDist N v ≤ physDist N w)
    (θ₁ θ₂ : ℝ) (hθ₂ : θ₁ + ∑ e ∈ Finset.univ \ edgesIn N T, edgeWeight N e ≤ θ₂)
    (hT : IsSinkLike N f T θ₁ θ₂) :
    IsSinkLike N f (insert v T) θ₁
      (θ₂ - ∑ e ∈ edgesIn N (insert v T) \ edgesIn N T, edgeWeight N e) := by sorry

end IDEPoA
