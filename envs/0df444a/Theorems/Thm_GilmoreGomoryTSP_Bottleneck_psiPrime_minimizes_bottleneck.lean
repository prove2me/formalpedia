-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_psiPrime_minimizes_bottleneck
-- name    : GilmoreGomoryTSP.Bottleneck.psiPrime_minimizes_bottleneck
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:08.439775+00:00
-- url     : https://prove2.me/theorems/038893ba-0f51-407d-8219-d5224b56519a
-- title:
--   The bottleneck case, pp. 670–671 — ψ′ is a tour minimizing the largest changeover cost
-- statement:
--   Let $N=n+1$ jobs have starting states $A_i$ and final states $B_i$, numbered so that $B_1\le\dots\le B_N$. Let $f\ge0$ be locally integrable and $g = 0$, so that the changeover cost (1) is
--   $$c_{ij} = \begin{cases}\int_{B_i}^{A_j} f(x)\,dx & A_j\ge B_i,\\ 0 & B_i>A_j.\end{cases}$$
--   Let $\varphi$ be a permutation ranking the $A$'s, let $T$ be a minimum spanning tree of $G_\varphi$ made of arcs $R_{q,q+1}$, where $R_{q,q+1}$ costs $c_{q\varphi(q+1)}$, and let
--   $$\psi' = \varphi\,\alpha_{j_1 j_1+1}\cdots\alpha_{j_m j_m+1},\qquad j_1<\dots<j_m \text{ the arcs of } T.$$
--   Then $\psi'$ is a tour, and for every tour $\psi$,
--   $$ m(\psi') = \max_i c_{i\psi'(i)} \;\le\; m(\psi) = \max_i c_{i\psi(i)}.$$
--
--   This solves the bottleneck traveling salesman problem for this cost matrix: a minimum (sum) spanning tree computation followed by interchanges applied in increasing order yields a tour whose largest changeover cost is as small as possible.
--
--   **Formalization Note** The cost keeps the general two-density form (1) with the hypotheses $f\ge0$, $g\equiv0$ and $f$ locally integrable. The tree is a minimum-*sum* spanning tree under the costs $c_{q\varphi(q+1)}$, as on the page, quantified over all adjacent-arc spanning trees; any such tree may be used. The interchanges are applied in increasing index order, the first one directly to $\varphi$. "Minimizes $m(\psi')$" is read as: $\psi'$ is a tour and $m(\psi')\le m(\psi)$ for every tour $\psi$. The paper's remark that the results hold equally for $f = 0$, $g\ge0$ is not formalized.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), pp. 670–671, Section "The bottleneck case"

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem psiPrime_minimizes_bottleneck {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    GilmoreGomoryTSP.MinCost.IsTour (psiPrime φ T) ∧
      ∀ ψ : Equiv.Perm (Fin (n + 1)), GilmoreGomoryTSP.MinCost.IsTour ψ → m f g A B (psiPrime φ T) ≤ m f g A B ψ := by sorry

end GilmoreGomoryTSP.Bottleneck
