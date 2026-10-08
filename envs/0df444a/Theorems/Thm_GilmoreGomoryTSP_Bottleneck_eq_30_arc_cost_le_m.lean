-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_eq_30_arc_cost_le_m
-- name    : GilmoreGomoryTSP.Bottleneck.eq_30_arc_cost_le_m
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:24.399411+00:00
-- url     : https://prove2.me/theorems/d986dd89-57dc-4870-9a93-dcb1c00ea1d9
-- title:
--   Eq. (30) — an arc R_{q,q+1} of G_ψ* outside G_φ has cost c_{qφ(q+1)} ≤ m(ψ)
-- statement:
--   Let the jobs be numbered so that $B_1\le\dots\le B_N$, let $f\ge 0$ be locally integrable and $g = 0$, so that $c_{ij} = \int_{B_i}^{A_j} f$ if $A_j\ge B_i$ and $c_{ij}=0$ otherwise. Let $\varphi$ rank the $A$'s ($j>i \Rightarrow A_{\varphi(j)}\ge A_{\varphi(i)}$) and let $\psi$ be any tour. If $R_{q,q+1}$ is an arc of $G_\psi^*$ that is not an arc of $G_\varphi$, then
--   $$ m(\psi) \;\ge\; c_{q\varphi(q+1)}. \tag{30}$$
--
--   It follows that every tour $\psi$ determines a spanning tree of $G_\varphi$, chosen among the arcs of $G_\psi^*$, all of whose arcs have bottleneck cost at most $m(\psi)$.
--
--   **Formalization Note** "Not in $G_\varphi$" is the hypothesis that $q$ and $q+1$ are not adjacent in $G_\varphi$, i.e. $\varphi(q)\ne q+1$ and $\varphi(q+1)\ne q$; "an arc of $G_\psi^*$" is that $q$ is one of the added arcs (22a)/(22b). The cost uses the general formula (1) with $g$ assumed identically $0$; $f$ is locally integrable so that the interval integrals are genuine.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 670, Eq. (30)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem eq_30_arc_cost_le_m {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (ψ : Equiv.Perm (Fin (n + 1))) (hψ : GilmoreGomoryTSP.MinCost.IsTour ψ) (q : Fin n) (hq : q ∈ starArcs φ ψ)
    (hq' : ¬ (graphOf φ).Adj q.castSucc q.succ) :
    arcCost f g A B φ q ≤ m f g A B ψ := by sorry

end GilmoreGomoryTSP.Bottleneck
