-- Prove2me | Theorems.Thm_MinrankTW_lemma_1
-- name    : MinrankTW.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:13.540147+00:00
-- url     : https://prove2.me/theorems/4c8fda18-2f63-411e-b53f-97b286bb24c9
-- title:
--   Lemma 1 — rank of a completed matrix: $\operatorname{rank}M=\operatorname{rank}A_1+\operatorname{rank}A_2+a+\dim R(0)-\dim K(R)$
-- statement:
--   Order the rows and columns of a matrix $M$ over $\mathbb F_q$ as $(I_1\mid B\mid I_2)$ and write
--   $$
--   M=\begin{pmatrix}A_1&U_1&0\\ V_1&W_1+W_2&V_2\\ 0&U_2&A_2\end{pmatrix},
--   $$
--   where the blocks $A_i$ may be rectangular and the boundary $B$ has $a$ columns and $c$ rows. For $i=1,2$ let
--   $$
--   R_i=\{(x,y)\in\mathbb F_q^a\oplus\mathbb F_q^c : \exists x_i,\ A_ix_i+U_ix=0,\ y=V_ix_i+W_ix\},
--   $$
--   where $x_i$ has one coordinate per column of $A_i$, put $R=R_1\boxplus R_2$ and $K(R)=\{x:(x,0)\in R\}$. Then
--   $$
--   \operatorname{rank}M=\operatorname{rank}A_1+\operatorname{rank}A_2+a+\dim R(0)-\dim K(R).
--   $$
--
--   The linear relation and the interior rank of one side therefore determine its effect on the rank of every completion; this is why the dynamic program may group partial assignments by these two quantities.
--
--   **Formalization Note** The identity is stated over the integers.
--
--   Differences from the source:
--   - encoding: M ordered as (I1 | B | I2) with blocks (11) → block matrix assembled from the nine blocks on rows ι₁ ⊕ (ρ ⊕ ι₂) and columns κ₁ ⊕ (β ⊕ κ₂); reason: the same matrix; any row/column order is a relabelling
--   - encoding: identity (12) between natural numbers → identity in ℤ; reason: the right side contains a subtraction; same content
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Lemma 1, p.10, Eqs. (11)–(12)

import Mathlib
import Definitions.Def_MinrankTW_LinRel
import Definitions.Def_MinrankTW_relJoin
import Definitions.Def_MinrankTW_relOfBlocks

namespace MinrankTW

open Matrix

/-- **Lemma 1** (Rank of a completed matrix), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.10, Eqs. (11)–(12). Order the rows as
`(I₁ | B | I₂)` and the columns likewise and write
`M = [[A₁, U₁, 0], [V₁, W₁ + W₂, V₂], [0, U₂, A₂]]`, with rectangular blocks; the boundary has
`a` columns and `c` rows. With `R_i = {(x, y) : ∃ x_i, A_i x_i + U_i x = 0, y = V_i x_i + W_i x}`,
`R = R₁ ⊞ R₂` and `K(R) = {x : (x, 0) ∈ R}`,
`rank M = rank A₁ + rank A₂ + a + dim R(0) − dim K(R)`.

**Formalization Note** Interior rows/columns of side `i` are the types `ιᵢ`/`κᵢ`, boundary
columns `β` (`a = |β|`) and boundary rows `ρ` (`c = |ρ|`). `M` is assembled with
`fromBlocks`, `fromRows`, `fromCols` on rows `ι₁ ⊕ (ρ ⊕ ι₂)` and columns `κ₁ ⊕ (β ⊕ κ₂)`.
The identity is stated in `ℤ`. -/
theorem lemma_1 {F : Type} [Field F] [Fintype F] {ι₁ κ₁ ι₂ κ₂ β ρ : Type} [Fintype ι₁] [Fintype κ₁]
    [Fintype ι₂] [Fintype κ₂] [Fintype β] [Fintype ρ]
    (A₁ : Matrix ι₁ κ₁ F) (U₁ : Matrix ι₁ β F) (V₁ : Matrix ρ κ₁ F) (W₁ W₂ : Matrix ρ β F)
    (V₂ : Matrix ρ κ₂ F) (U₂ : Matrix ι₂ β F) (A₂ : Matrix ι₂ κ₂ F) :
    ((fromBlocks A₁ (fromCols U₁ 0) (fromRows V₁ 0) (fromBlocks (W₁ + W₂) V₂ U₂ A₂)).rank : ℤ) =
      (A₁.rank : ℤ) + A₂.rank + Fintype.card β +
        Module.finrank F (relZero (relJoin (relOfBlocks A₁ U₁ V₁ W₁) (relOfBlocks A₂ U₂ V₂ W₂))) -
        Module.finrank F (relKer (relJoin (relOfBlocks A₁ U₁ V₁ W₁) (relOfBlocks A₂ U₂ V₂ W₂))) := by sorry

end MinrankTW
