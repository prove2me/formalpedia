-- Prove2me | Theorems.Thm_NicerEars_TwoEC_proposition_4
-- name    : NicerEars.TwoEC.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:49.531996+00:00
-- url     : https://prove2.me/theorems/9907d885-3784-4edf-a98f-077a4860d072
-- title:
--   Proposition 4 — OPT(G,T), OPT₂EC(G) and LP(G,T) are additive over a cut vertex
-- statement:
--   Let $G_1$ and $G_2$ be connected graphs with $V(G_1)\cap V(G_2)=\{v\}$, let $G:=(V(G_1)\cup V(G_2),E(G_1)\cup E(G_2))$, and let $T\subseteq V(G)$ with $|T|$ even. For $i=1,2$ let $T_i$ be the even set among $(T\cap V(G_i))\setminus\{v\}$ and $(T\cap V(G_i))\cup\{v\}$. Then
--
--   $$\mathrm{OPT}(G,T)=\mathrm{OPT}(G_1,T_1)+\mathrm{OPT}(G_2,T_2),\qquad \mathrm{OPT}_{2EC}(G)=\mathrm{OPT}_{2EC}(G_1)+\mathrm{OPT}_{2EC}(G_2),$$
--   $$\mathrm{LP}(G,T)=\mathrm{LP}(G_1,T_1)+\mathrm{LP}(G_2,T_2).$$
--
--   Hence approximation guarantees and integrality ratios proved for the blocks of a graph transfer to the graph, and the paper's algorithms may assume that $G$ is 2-vertex-connected.
--
--   **Formalization Note** $G$ is built as the one-vertex sum of $G_1$ and $G_2$ glued at $v_1\in V(G_1)$ and $v_2\in V(G_2)$ (the definition `OneSum`). The page prints the last identity as "$\mathrm{LP}(G,T)=\mathrm{LP}(G,T_1)+\mathrm{LP}(G,T_2)$"; its proof on p. 6 shows $\mathrm{LP}(G_1,T_1)+\mathrm{LP}(G_2,T_2)$ is meant, which is what is stated. The closing "in particular" sentence is informal and not formalized. The LP values are infima of the objective over the feasible sets, which are nonempty for connected graphs.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 5, Proposition 4 (proof p. 6)

import Mathlib
import Definitions.Def_NicerEars_TwoEC_OneSum

namespace NicerEars.TwoEC

open Finset

theorem proposition_4 {V₁ V₂ E₁ E₂ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype V₂]
    [DecidableEq V₂] [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]
    (G₁ : Graph V₁ E₁) (G₂ : Graph V₂ E₂) (hG₁ : G₁.IsConnected) (hG₂ : G₂.IsConnected)
    (v₁ : V₁) (v₂ : V₂) (T : Finset (V₁ ⊕ {w : V₂ // w ≠ v₂})) (hT : Even #T) :
    (oneSum G₁ G₂ v₁ v₂).OPT T =
        G₁.OPT (evenAmong v₁ (restrictLeft v₂ T)) +
          G₂.OPT (evenAmong v₂ (restrictRight v₁ v₂ T)) ∧
      (oneSum G₁ G₂ v₁ v₂).OPT2EC = G₁.OPT2EC + G₂.OPT2EC ∧
      (oneSum G₁ G₂ v₁ v₂).lpTValue T =
        G₁.lpTValue (evenAmong v₁ (restrictLeft v₂ T)) +
          G₂.lpTValue (evenAmong v₂ (restrictRight v₁ v₂ T)) := by sorry

end NicerEars.TwoEC
