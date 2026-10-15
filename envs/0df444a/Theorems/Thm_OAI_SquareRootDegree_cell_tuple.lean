-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_cell_tuple
-- name    : OAI.SquareRootDegree.cell_tuple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:44:32.612113+00:00
-- url     : https://prove2.me/theorems/8234f4d5-c8e0-48cf-a35b-a5763c9ae263
-- title:
--   The indicator of a tuple of observations is the product of the coordinate indicators
-- statement:
--   For a map $F:\alpha\to\beta$ between arbitrary sets and a value $b\in\beta$, write $\mathbf 1[F=b]:\alpha\to\mathbb R$ for the real indicator of the cell $F^{-1}(b)$, so $\mathbf 1[F=b](x)=1$ if $F(x)=b$ and $0$ otherwise.
--
--   Let $\kappa$ be a finite index set and $F_i:\alpha\to\beta$ ($i\in\kappa$) a family of maps, combined into the tuple map $\mathbf F:\alpha\to\beta^\kappa$, $\mathbf F(x)=(F_i(x))_{i\in\kappa}$. Then for every target tuple $b=(b_i)_{i\in\kappa}\in\beta^\kappa$ and every $x\in\alpha$,
--
--   $$
--   \mathbf 1[\mathbf F=b](x)=\prod_{i\in\kappa}\mathbf 1[F_i=b_i](x).
--   $$
--
--   Thus the cell of a joint observation is the intersection of the cells of its components, written multiplicatively. When $\alpha$ is a Boolean cube, combining this with the subadditivity of Fourier degree under products bounds the degree of the indicator of a joint observation by the sum of the degrees of the individual indicators.
--
--   **Formalization Note** The indicator is `cell F b x`, defined using classical decidability of equality. No finiteness is needed for $\alpha$ or $\beta$, only for $\kappa$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean#L66-L82

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks

open OAI OAI.SquareRootDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.SquareRootDegree.cell_tuple {α β κ : Type*} [Fintype κ] (F : κ → α → β) (b : κ → β) (x : α) :
    cell (fun x i => F i x) b x = ∏ i, cell (F i) (b i) x := by sorry
