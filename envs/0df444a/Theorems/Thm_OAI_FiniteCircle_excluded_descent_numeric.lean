-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_descent_numeric
-- name    : OAI.FiniteCircle.excluded_descent_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:42:54.816253+00:00
-- url     : https://prove2.me/theorems/85011a4f-d4f2-4c05-ade3-d10f4a9af552
-- title:
--   Numerical estimate: the excluded-coordinate descent bound at level $n^4$ dominates $n^{-3n^4}$
-- statement:
--   For natural numbers $m,K,T,B,s,l$ define the pair reset budget and the pair descent bound
--
--   $$
--   b(K,T,s,l)=\Big\lfloor\frac{s+lT+K-3}{K-2}\Big\rfloor,\qquad D(m,K,T,B,s,l)=\frac{1}{4^{l}\,B^{\,l+3b(K,T,s,l)}\,m^{5K}},
--   $$
--
--   with natural-number subtraction and floor division.
--
--   Let $n\ge10^6$ be an integer such that $n^4$ is even (equivalently, $n$ is even), and put $N=n^4$ and $K=\lfloor N/100\rfloor$. Then
--
--   $$
--   \frac{1}{n^{3n^4}}\le\frac{1}{2^{N}\cdot4}\;D\big(N,K,n^3,n,1,N\big)=\frac{1}{2^{N}\cdot4\cdot4^{N}\,n^{\,N+3b(K,n^3,1,N)}\,N^{5K}}.
--   $$
--
--   This is the purely numerical step of the lower bound for excluded-coordinate circle words: the excluded denominator descent (with $m=N$, $T=n^3$, $B=n$) bounds the top-level excluded phase cost of the half turn from below by $D(N,K,n^3,n,1,N)$, the excluded separation inequality loses a further factor $1/(2^N\cdot4)$, and this estimate converts the product into the clean quantity $n^{-3n^4}$.
--
--   **Formalization Note** $D$ is `pairDescentBound` and $b$ is `pairResetBudget`; the evenness hypothesis is stated as $n^4=2\lfloor n^4/2\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean#L289-L312

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

theorem OAI.FiniteCircle.excluded_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * pairDescentBound (n^4) (n^4/100) (n^3) n 1 (n^4) := by sorry
