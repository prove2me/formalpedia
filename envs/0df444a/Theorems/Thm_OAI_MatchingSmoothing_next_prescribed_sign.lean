-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_next_prescribed_sign
-- name    : OAI.MatchingSmoothing.next_prescribed_sign
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:32:01.772854+00:00
-- url     : https://prove2.me/theorems/b9cfd93c-29a9-4437-995e-b04ddfae8b63
-- title:
--   Adding one more prescribed sign to a joint eigenvector of standard-pair transpositions
-- statement:
--   Fix $h\in\mathbb N$ and let $V_h=\{0,\dots,h-1\}\times\{0,1\}$, a set of $2h$ vertices grouped into the *standard pairs* $\{(i,0),(i,1)\}$. Let $\tau_i$ be the transposition of $V_h$ that swaps $(i,0)$ and $(i,1)$. For distinct vertices $a,b$, let $\tau_{ab}$ be the transposition of $a$ and $b$. Let $\mathcal P_h$ be the finite set of perfect matchings of $V_h$, viewed as fixed-point-free involutions $M$ of $V_h$. The symmetric group $\mathrm{Sym}(V_h)$ acts on $\mathcal P_h$ by $p\cdot M=pMp^{-1}$, and hence linearly on functions $F:\mathcal P_h\to\mathbb R$ by
--
--   $$
--   (p\cdot F)(M)=F(p^{-1}Mp).
--   $$
--
--   For $t\in\mathbb N$ write $V_{<t}=\{(i,\beta)\in V_h:\ i<t\}$ for the vertices of the first $t$ standard pairs.
--
--   Let $W\subseteq\mathbb R^{\mathcal P_h}$ be a linear subspace with $p\cdot F\in W$ for every $p\in\mathrm{Sym}(V_h)$ and every $F\in W$. Let $t<h$, let $\chi:\{0,\dots,h-1\}\to\mathbb R$ and $c\in\{1,-1\}$. Let $f\in W$ satisfy $\tau_i\cdot f=\chi(i)\,f$ for all $i<t$, and suppose that there are distinct vertices $a,b\notin V_{<t}$ with $f+c\,(\tau_{ab}\cdot f)\ne0$. Then there is a nonzero $g\in W$ such that
--
--   $$
--   \tau_t\cdot g=c\,g\qquad\text{and}\qquad \tau_i\cdot g=\chi(i)\,g\quad\text{for all }i<t .
--   $$
--
--   So a vector with prescribed eigenvalues for the swaps of the first $t$ standard pairs can be upgraded to one that also has the prescribed sign $c$ for the swap of pair $t$. The only condition is that the $\pm$ symmetrisation of $f$ under some transposition outside the first $t$ pairs does not vanish. Iterating this step builds nonzero vectors in invariant subspaces with any desired $\pm1$ pattern on the first few standard pairs. This is the engine of the dimension lower bound for invariant spaces of high-degree functions on matchings.
--
--   **Formalization Note** $V_h$ is `Fin h × Bool`, $\tau_i$ is `pairSwap i`, $V_{<t}$ is `firstVertices h t`, and $p\cdot F$ is `Pairing.act p F`, defined through `relabel`. The function $\chi$ is an arbitrary real-valued function; it enters only through the eigenvalue equations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean#L56-L106

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension

open OAI OAI.MatchingSmoothing
universe u_1
variable {h : ℕ}

theorem OAI.MatchingSmoothing.next_prescribed_sign (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    {t : ℕ} (ht : t < h) (χ : Fin h → ℝ) (c : ℝ) (hc : c = 1 ∨ c = -1)
    (f : Pairing (Vertices h) → ℝ) (hf : f ∈ W)
    (heig : ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f)
    (hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
      f + c • Pairing.act (Equiv.swap a b) f ≠ 0) :
    ∃ g ∈ W, g ≠ 0 ∧ Pairing.act (pairSwap ⟨t, ht⟩) g = c • g ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) g = χ i • g := by sorry
