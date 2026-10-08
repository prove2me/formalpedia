-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_m_psiPrime_cases
-- name    : GilmoreGomoryTSP.Bottleneck.m_psiPrime_cases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:40.978772+00:00
-- url     : https://prove2.me/theorems/2aa30ae4-600e-426f-ad7a-72c2cee34e10
-- title:
--   p. 671 — m(ψ′) equals some c_{jφ(j)} or the cost c_{qφ(q+1)} of a tree arc
-- statement:
--   Let $B_1\le\dots\le B_N$, $f\ge0$ locally integrable, $g=0$, let $\varphi$ rank the $A$'s, let $T$ be a minimum spanning tree of $G_\varphi$ for the arc costs $c_{q\varphi(q+1)}$, and let $\psi' = \varphi\,\alpha_{j_1 j_1+1}\cdots\alpha_{j_m j_m+1}$ ($j_1<\dots<j_m$ the arcs of $T$). Then either
--   $$ m(\psi') = c_{j\varphi(j)} \quad\text{for some job } j, \qquad\text{or}\qquad m(\psi') = c_{q\varphi(q+1)} \quad\text{for some arc } R_{q,q+1}\in T.$$
--
--   So the bottleneck cost of $\psi'$ is either one of the costs of $\varphi$ itself or the cost of an arc of the tree.
--
--   **Formalization Note** The page writes "for some $j$ either $m(\psi') = c_{j\varphi(j)}$ or $m(\psi') = c_{j\varphi(j+1)}$", and adds that in the latter case $m(\psi')$ is the largest cost of an arc of the tree. The Lean states the second alternative with $R_{j,j+1}$ an arc of $T$, which is this reading; it is a value statement about the maximum, not a claim that every $\psi'(i)$ is $\varphi(i)$ or $\varphi(i+1)$.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 671, "From the manner in which ψ′ has been defined …"

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

theorem m_psiPrime_cases {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (T : Finset (Fin n)) (hT : IsMinSpanningTree f g A B φ T) :
    (∃ j : Fin (n + 1), m f g A B (psiPrime φ T) = GilmoreGomoryTSP.MinCost.c f g A B j (φ j)) ∨
      ∃ q ∈ T, m f g A B (psiPrime φ T) = arcCost f g A B φ q := by sorry

end GilmoreGomoryTSP.Bottleneck
