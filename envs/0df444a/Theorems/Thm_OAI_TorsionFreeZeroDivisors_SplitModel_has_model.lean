-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_SplitModel_has_model
-- name    : OAI.TorsionFreeZeroDivisors.SplitModel.has_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T01:09:00.275034+00:00
-- url     : https://prove2.me/theorems/3b0c88a5-1ee4-42ad-a16b-a5c3cbd0930e
-- title:
--   Corollary 5.3 (OpenAI), relation-module form — a presentation whose relation module splits gives a finite two-dimensional K(G,1)
-- statement:
--   Let $G$ be a group, given the discrete topology, and let $s:S\to G$ and relators $w:Q\to F(S)$ present it: every relator maps to $1$ under the induced map $F(S)\to G$, that map is surjective, and its kernel is the normal closure of the relators. Write $\partial(w_i)\in\mathbb Z[G\times S]$ for the Fox derivative of $w_i$ (`CellModule.fox`). Suppose there is an additive map
--   $$L:\mathbb Z[G\times S]\to\mathbb Z[G\times Q]\quad\text{with}\quad L\big(g\cdot\partial(w_i)\big)=(g,i)\ \text{ for all } g\in G,\ i\in Q,$$
--   where $g\cdot$ is the left translation `CellModule.translate`. Then, if $S$ and $Q$ are finite and $Q$ is nonempty, $G$ has a finite two-dimensional classifying space.
--
--   The conclusion is `OAI.TorsionFreeZeroDivisors.HasFiniteTwoDimensionalClassifyingSpace G`, from the goal's own bundle. It asks for a Hausdorff, path-connected space $X$ with a finite CW structure that has no cells above dimension $2$ and at least one $2$-cell. It also asks for a basepoint $x$ with $G\cong\pi_1(X,x)$, and a contractible space $E$ with a surjective covering map $E\to X$.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 23: “Corollary 5.3. The universal cover of $X$ is contractible, and $G$ is torsion-free.” The proof says that the simply connected two-dimensional cover has $H_2=0$ and $H_1=0$, and so is contractible by Whitehead's theorem. In OpenAI's Lean that step is this criterion. The map $L$ is a left inverse of the boundary map from $2$-chains to $1$-chains of the cover of the presentation complex, which forces $H_2=0$. The construction applies it to the coned graph presentation, with $L$ supplied by the relation-area splitting of Section 5.
--
--   **Formalization note.** This is OpenAI's `SplitModel.has_model` with its statement unchanged. The space is OpenAI's presentation complex (`IndexedCells.Base`) and the cover is its Cayley-complex cover (`IndexedCells.Cover`), but neither appears in the statement, which only asserts the existence of such spaces. The topology on $G$ is only an instance argument: discrete, it is the one the cover's construction uses.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 23, Corollary 5.3 (the universal cover of X is contractible), in the relation-module form of its proof; Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), SplitModel.has_model

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisors
import Definitions.Def_TFZDCellModule

namespace OAI.TorsionFreeZeroDivisors.SplitModel

theorem has_model {G S Q : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (s : S → G) (w : Q → FreeGroup S) (hw : ∀ i, FreeGroup.lift s (w i) = 1)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure (Set.range w))
    (L : CellModule.Module G S →+ CellModule.Module G Q)
    (hL : ∀ g i, L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i))) =
      Finsupp.single (g, i) 1)
    [Finite S] [Finite Q] [Nonempty Q] :
    HasFiniteTwoDimensionalClassifyingSpace G := by
  sorry

end OAI.TorsionFreeZeroDivisors.SplitModel
