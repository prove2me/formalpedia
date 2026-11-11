-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_17
-- name    : GaussLocalMaxColoring.Main.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:20:56.991201+00:00
-- url     : https://prove2.me/theorems/7d4cc998-51b4-4e0e-b17f-4c7f1f772dab
-- title:
--   Lemma 17 — $p_F(x)=\mathbb E_g[\overline\Phi(M_F(x)/\sqrt3)]$ and $\mathbb P_g[M_F(x)\le a]\le p_F(x)/\overline\Phi(a/\sqrt3)$
-- statement:
--   Let $\{v_x\}$ be a strict vector 3-coloring of a graph $G$ (unit vectors in $\mathbb R^d$, $\langle v_x,v_y\rangle=-\tfrac12$ on edges), $F\subseteq V$ and $x\in F$. Then for every $a\in\mathbb R$,
--   $$p_F(x)=\mathbb E_g\big[\overline\Phi(M_F(x)/\sqrt3)\big],\qquad \mathbb P_g[M_F(x)\le a]\le\frac{p_F(x)}{\overline\Phi(a/\sqrt3)},$$
--   where $p_F(x)=\mathbb P_g[x\in I_F(g)]$, $M_F(x)=\max_{y\in N_F(x)}\langle g,v_{xy}\rangle$ ($-\infty$ for an empty neighborhood, with $\overline\Phi(-\infty)=1$) and $\overline\Phi=1-\Phi$ is the standard normal upper tail.
--
--   Differences from the source:
--   - generalization: §4 standing assumptions: G is the 3-colorable input graph with every degree ≤ n^β, with a strict vector 3-coloring → any graph G on Fin n with a strict vector 3-coloring, any dimension d; reason: the proof uses only Equation (3); the §4 setting is an instance
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
--   - encoding: M_F(x) = −∞ when N_F(x) = ∅ → nbrMax in WithBot ℝ (⊥), tailOver c ⊥ = 1 = Φ̄(−∞); reason: an empty maximum must not default to 0
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 17, printed p. 17 (PDF 19)

import Mathlib
import Definitions.Def_RecGaussColoring_Main_Rounding
import Definitions.Def_GaussLocalMaxColoring_Main_Basic

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 17** (p. 17, PDF 19). Let `{v_x}` be a strict vector 3-coloring of `G`, `F ⊆ V` and
`x ∈ F`. Then for every `a ∈ ℝ`, `p_F(x) = E_g[Φ̄(M_F(x)/√3)]` and
`P_g[M_F(x) ≤ a] ≤ p_F(x)/Φ̄(a/√3)`; `M_F(x) = −∞` (`⊥`) and `Φ̄(−∞) = 1` when `N_F(x) = ∅`. -/
theorem lemma_17 {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d)
    (hv : StrictVectorColoring G v) (F : Finset (Fin n)) (x : Fin n) (hx : x ∈ F) (a : ℝ) :
    pLocal G v F x =
        ∫ g, tailOver (Real.sqrt 3) (nbrMax G v F x g) ∂(stdGaussian (Space d)) ∧
      gaussProb {g : Space d | nbrMax G v F x g ≤ ((a : ℝ) : WithBot ℝ)} ≤
        pLocal G v F x / PhiTail (a / Real.sqrt 3) := by sorry

end GaussLocalMaxColoring.Main
