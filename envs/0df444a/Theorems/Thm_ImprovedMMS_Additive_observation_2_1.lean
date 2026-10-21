-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_observation_2_1
-- name    : ImprovedMMS.Additive.observation_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:48.504127+00:00
-- url     : https://prove2.me/theorems/34974e68-8e4d-45ab-b0d0-26b2bd17121a
-- title:
--   Observation 2.1, p. 13 — if every α-irreducible instance admits an α-MMS allocation, every instance does
-- statement:
--   Let $n$ agents have additive valuations $V_i$ (each $V_i(S)=\sum_{b\in S}V_i(\{b\})$ with $V_i\ge 0$) over a finite set of goods, and fix $\alpha\in\mathbb R$. Consider all instances $(\mathcal N,\mathcal M)$ formed by a non-empty set $\mathcal N$ of these agents and a set $\mathcal M$ of goods. If every $\alpha$-irreducible instance admits an $\alpha$-MMS allocation, then every instance does:
--   $$\Big(\forall(\mathcal N,\mathcal M)\ \alpha\text{-irreducible}:\ \exists\ \alpha\text{-MMS allocation}\Big)\ \Longrightarrow\ \forall(\mathcal N,\mathcal M):\ \exists\ \alpha\text{-MMS allocation}.$$
--
--   This is the reduction that lets the paper assume irreducibility throughout §3.
--
--   **Formalization Note** Instances are sub-instances `(N, M)` of the ambient agents `Fin n` and goods `Fin m`, with the same valuations `v`; the hypothesis ranges only over these, which is all the paper's argument uses, so the statement implies the page's. Instances without agents are excluded (`N.Nonempty`): with no agent and at least one good no allocation exists and the instance is irreducible, so the hypothesis would fail and the statement would be vacuous.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 13, Observation 2.1

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance
open LittleCharity.MMS

namespace ImprovedMMS.Additive

/-- Observation 2.1 (p. 13): for additive agents, if every `α`-irreducible instance admits an
`α`-MMS allocation then every instance does. Instances are the pairs `(N, M)` of a non-empty set
of agents and a set of goods, the agents keeping their valuations `v`. -/
theorem observation_2_1 {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : IsAdditive v)
    (h : ∀ (N : Finset (Fin n)) (M : Finset (Fin m)), N.Nonempty →
      IsIrreducible α v N M → AdmitsMMSAlloc α v N M) :
    ∀ (N : Finset (Fin n)) (M : Finset (Fin m)), N.Nonempty → AdmitsMMSAlloc α v N M := by sorry

end ImprovedMMS.Additive
