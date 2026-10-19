-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_three_table_kernel_moment
-- name    : OAI.MatchingSmoothing.three_table_kernel_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:39:11.741724+00:00
-- url     : https://prove2.me/theorems/1d46c7a1-6201-4619-8a32-852ebe202257
-- title:
--   Polynomial second-moment bound for the table-class kernel of 3-colourings
-- statement:
--   Let $H$ be a nonempty finite set and $V=H\times\{0,1\}$, with standard pairs $\{(i,0),(i,1)\}$, $i\in H$. For a $3$-colouring $f:V\to\{0,1,2\}$, let $h_f(a)$ be the number of vertices of colour $a$. Its *table* $T_f$ assigns to each of the six unordered colour pairs $\{a,b\}$ the number of standard pairs $i$ with $\{f(i,0),f(i,1)\}=\{a,b\}$. Fix a reference colouring $f_0$ that uses every colour, i.e. $h_{f_0}(a)>0$ for $a=0,1,2$, and set
--
--   $$
--   Z=\#\{f:V\to\{0,1,2\}:\ h_f=h_{f_0}\},\qquad D=\#\{f:V\to\{0,1,2\}:\ T_f=T_{f_0}\},
--   $$
--
--   $$
--   N(\sigma)=\#\{f:V\to\{0,1,2\}:\ T_f=T_{f_0}\ \text{ and }\ T_{f\circ\sigma}=T_{f_0}\}\qquad(\sigma\in\mathrm{Sym}(V)).
--   $$
--
--   Then
--
--   $$
--   \sum_{\sigma\in\mathrm{Sym}(V)}\Big(\frac{Z}{D^2}\,N(\sigma)\Big)^2\ \le\ |\mathrm{Sym}(V)|\cdot(|H|+1)^{33}.
--   $$
--
--   The condition $T_{f\circ\sigma}=T_{f_0}$ says that, under $f$, the matching with edges $\{\sigma(i,0),\sigma(i,1)\}$ has the same type counts as the standard matching has under $f_0$. Let $f$ be uniform among the $Z$ colourings with the colour counts of $f_0$. Then the events $T_f=T_{f_0}$ and $T_{f\circ\sigma}=T_{f_0}$ each have probability $D/Z$, and their intersection has probability $N(\sigma)/Z$. So $\frac{Z}{D^2}N(\sigma)$ is the ratio of the joint probability to the product of the two probabilities; it would equal $1$ if the events were independent. The theorem says that the mean square of this ratio over a uniformly random $\sigma$ is at most $(|H|+1)^{33}$, polynomial in the number of pairs. This is the moment estimate behind the trace bound for the incidence operator between perfect matchings and colourings.
--
--   **Formalization Note** $Z$ is the cardinality of `Colorings (H × Bool) (Fin 3) (histogram f₀)` and the table is `threeTable`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean#L301-L357

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10
open Matrix
variable {H : Type u_10} [Fintype H] [DecidableEq H]

theorem OAI.MatchingSmoothing.three_table_kernel_moment (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    (∑ σ : Equiv.Perm (H × Bool),
      ((Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) : ℝ) /
        (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) ^ 2 *
        Fintype.card {f : H × Bool → Fin 3 //
          threeTable f = threeTable f₀ ∧ threeTable (f ∘ σ) = threeTable f₀}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * (Fintype.card H + 1 : ℝ) ^ 33 := by sorry
