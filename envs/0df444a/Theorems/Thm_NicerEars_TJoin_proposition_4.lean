-- Prove2me | Theorems.Thm_NicerEars_TJoin_proposition_4
-- name    : NicerEars.TJoin.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:26.936533+00:00
-- url     : https://prove2.me/theorems/98ea9b80-4e56-4cc3-b93f-5934b657f144
-- title:
--   Proposition 4 — OPT(G,T), OPT_2EC(G) and LP(G,T) are additive over a cut vertex
-- statement:
--   Let $G_1$ and $G_2$ be connected graphs with $V(G_1)\cap V(G_2)=\{v\}$, let $G:=(V(G_1)\cup V(G_2),E(G_1)\cup E(G_2))$ and let $T\subseteq V(G)$ with $|T|$ even. For $i=1,2$ let $T_i$ be the even set among $(T\cap V(G_i))\setminus\{v\}$ and $(T\cap V(G_i))\cup\{v\}$. Then
--   $$\mathrm{OPT}(G,T)=\mathrm{OPT}(G_1,T_1)+\mathrm{OPT}(G_2,T_2),\qquad \mathrm{OPT}_{2EC}(G)=\mathrm{OPT}_{2EC}(G_1)+\mathrm{OPT}_{2EC}(G_2),\qquad \mathrm{LP}(G,T)=\mathrm{LP}(G_1,T_1)+\mathrm{LP}(G_2,T_2).$$
--
--   Here $\mathrm{OPT}_{2EC}(H)$ is the minimum number of edges of a 2-edge-connected spanning multi-subgraph of $H$ (a subgraph of $2H$).
--
--   This reduces the connected-$T$-join problem, its LP relaxation, and hence every approximation guarantee, to the blocks of $G$.
--
--   **Formalization Note.** $G$ is given with vertex sets $V_1\cup V_2=V(G)$, $V_1\cap V_2=\{v\}$ and a partition $E_1\sqcup E_2$ of its edges with every edge of $E_i$ inside $V_i$; $G_i$ is the sub-multigraph $(V_i,E_i)$. Each identity is stated as two inequalities between solutions: every connected-$T$-join of $G$ yields connected-$T_i$-joins of $G_i$ of no larger total size and conversely, and likewise for feasible points of the LPs; this is equivalent to the identities of the minima. The page prints $\mathrm{LP}(G,T)=\mathrm{LP}(G,T_1)+\mathrm{LP}(G,T_2)$; the proof on p. 6 states $\mathrm{LP}(G_1,T_1)+\mathrm{LP}(G_2,T_2)$, which is what is formalized. The closing "in particular" remark on approximation guarantees is a consequence and is not stated.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 4 (proof p. 6)

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proposition 4 (p. 5). `G` is the union of the connected graphs
`G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)` with `V₁ ∩ V₂ = {v}`; `Tᵢ` is the even set among
`(T ∩ Vᵢ) ∖ {v}` and `(T ∩ Vᵢ) ∪ {v}`. Then `OPT(G, T) = OPT(G₁, T₁) + OPT(G₂, T₂)`,
`OPT_2EC(G) = OPT_2EC(G₁) + OPT_2EC(G₂)` (2-edge-connected spanning multi-subgraphs, i.e. subsets
of 2G) and `LP(G, T) = LP(G₁, T₁) + LP(G₂, T₂)` (the page prints `LP(G, T₁) + LP(G, T₂)`; its proof on p. 6
states the corrected identity). Each identity is stated as its two inequalities between optimal
solutions: every solution on one side yields one on the other side of at most the same value. -/
theorem proposition_4 (G : Graph V E) (v : V) (V₁ V₂ : Finset V) (E₁ E₂ : Finset E)
    (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ) (hE₁₂ : Disjoint E₁ E₂)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (hG₁ : (G.sub V₁ E₁ h₁).IsConnected) (hG₂ : (G.sub V₂ E₂ h₂).IsConnected)
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁) (T₂ : Finset V₂)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (hT₂ : Even #T₂ ∧ (T₂.map (Function.Embedding.subtype _) = (T ∩ V₂).erase v ∨
      T₂.map (Function.Embedding.subtype _) = insert v (T ∩ V₂))) :
    -- OPT(G, T) ≥ OPT(G₁, T₁) + OPT(G₂, T₂)
    (∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F →
      ∃ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
        (G.sub V₁ E₁ h₁).IsConnectedTJoin T₁ F₁ ∧ (G.sub V₂ E₂ h₂).IsConnectedTJoin T₂ F₂ ∧
        #F₁ + #F₂ ≤ #F) ∧
    -- OPT(G, T) ≤ OPT(G₁, T₁) + OPT(G₂, T₂)
    (∀ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
      (G.sub V₁ E₁ h₁).IsConnectedTJoin T₁ F₁ → (G.sub V₂ E₂ h₂).IsConnectedTJoin T₂ F₂ →
      ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧ #F ≤ #F₁ + #F₂) ∧
    -- OPT_2EC(G) ≥ OPT_2EC(G₁) + OPT_2EC(G₂)
    (∀ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F →
      ∃ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
        (G.sub V₁ E₁ h₁).double.IsTwoECSpanning F₁ ∧ (G.sub V₂ E₂ h₂).double.IsTwoECSpanning F₂ ∧
        #F₁ + #F₂ ≤ #F) ∧
    -- OPT_2EC(G) ≤ OPT_2EC(G₁) + OPT_2EC(G₂)
    (∀ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
      (G.sub V₁ E₁ h₁).double.IsTwoECSpanning F₁ → (G.sub V₂ E₂ h₂).double.IsTwoECSpanning F₂ →
      ∃ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F ∧ #F ≤ #F₁ + #F₂) ∧
    -- LP(G, T) ≥ LP(G₁, T₁) + LP(G₂, T₂)
    (∀ x : E → ℝ, G.LPTFeasible T x →
      ∃ (x₁ : E₁ → ℝ) (x₂ : E₂ → ℝ), (G.sub V₁ E₁ h₁).LPTFeasible T₁ x₁ ∧
        (G.sub V₂ E₂ h₂).LPTFeasible T₂ x₂ ∧ ∑ e, x₁ e + ∑ e, x₂ e ≤ ∑ e, x e) ∧
    -- LP(G, T) ≤ LP(G₁, T₁) + LP(G₂, T₂)
    (∀ (x₁ : E₁ → ℝ) (x₂ : E₂ → ℝ), (G.sub V₁ E₁ h₁).LPTFeasible T₁ x₁ →
      (G.sub V₂ E₂ h₂).LPTFeasible T₂ x₂ →
      ∃ x : E → ℝ, G.LPTFeasible T x ∧ ∑ e, x e ≤ ∑ e, x₁ e + ∑ e, x₂ e) := by sorry

end NicerEars.TJoin
