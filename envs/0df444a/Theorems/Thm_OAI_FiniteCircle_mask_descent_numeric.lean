-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_descent_numeric
-- name    : OAI.FiniteCircle.mask_descent_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:42:25.411987+00:00
-- url     : https://prove2.me/theorems/5a6ac2e2-3409-490b-a342-48d5fb215b16
-- title:
--   Numerical estimate: the mask descent bound at level $n^4$ dominates $n^{-3n^4}$
-- statement:
--   For natural numbers $h,K,T,s,l$ define the reset budget and the descent bound
--
--   $$
--   r(K,T,s,l)=\Big\lfloor\frac{s+lT+K-2}{K-1}\Big\rfloor,\qquad \Delta(h,K,T,s,l)=\frac{1}{4^{l}\,T^{\,l+r(K,T,s,l)}\,h^{4K}},
--   $$
--
--   with natural-number subtraction and floor division.
--
--   Let $n\ge10^6$ be an integer such that $n^4$ is even (equivalently, $n$ is even), and put $N=n^4$ and $K=\lfloor N/100\rfloor$. Then
--
--   $$
--   \frac{1}{n^{3n^4}}\le\frac{1}{2^{N}\cdot4}\;\Delta\big(N,K,n^2,1,N\big)=\frac{1}{2^{N}\cdot4\cdot4^{N}\,(n^{2})^{\,N+r(K,n^2,1,N)}\,N^{4K}}.
--   $$
--
--   This is the purely numerical step of the lower bound for mask circle words: the mask denominator descent bounds the top-level mask phase cost of the half turn from below by $\Delta(N,K,n^2,1,N)$, the mask separation inequality loses a further factor $1/(2^N\cdot4)$, and this estimate converts the product into the clean quantity $n^{-3n^4}$.
--
--   **Formalization Note** $\Delta$ is `descentBound` and $r$ is `resetBudget`; the evenness hypothesis is stated as $n^4=2\lfloor n^4/2\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean#L264-L287

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.mask_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * descentBound (n^4) (n^4/100) (n^2) 1 (n^4) := by sorry
