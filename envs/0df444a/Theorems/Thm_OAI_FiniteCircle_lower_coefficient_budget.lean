-- Prove2me | Theorems.Thm_OAI_FiniteCircle_lower_coefficient_budget
-- name    : OAI.FiniteCircle.lower_coefficient_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:00:06.203034+00:00
-- url     : https://prove2.me/theorems/8704ec72-5de6-4be8-a82c-9415fa790adf
-- title:
--   Numerical budget $n^k\bigl(4n^4/(n^4)^{2n^4}+2J/(n^4/2)^{n^4}\bigr)\le 2^{-28}n^{-3n^4}$ when $n^4=4k$
-- statement:
--   Let $n,k,J$ be natural numbers with $n\ge 10^6$, $n^4=4k$ and $J\le n^{13}$. Then, as an inequality of real numbers,
--
--   $$
--   n^{k}\left(\frac{4n^4}{(n^4)^{2n^4}}+\frac{2J}{(n^4/2)^{n^4}}\right)\;\le\;\frac{2^{-28}}{n^{3n^4}} ,
--   $$
--
--   where $2^{-28}=1/268435456$.
--
--   This is the arithmetic core of the distortion lower bound. In the Fourier-analytic estimate with depth $h=n^4$, row-repetition factor $R=(n^4)^{2n^4}$, frequency threshold $B=(n^4/2)^{n^4}$ and $J=\lfloor\log_2 M\rfloor+1$ dyadic scales, the bracket is the loss factor $4h/R+2J/B$. The inequality says that even after multiplying this loss by the target distortion $n^k=n^{n^4/4}$, it stays below the relative separation $2^{-28}n^{-3n^4}$ available in the long direction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L216-L272

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.lower_coefficient_budget {n k J : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : J≤n^13) :
    (n:ℝ)^k * (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+
        2*J/(((n^4:ℕ):ℝ)/2)^(n^4)) ≤ (1/268435456)/(n:ℝ)^(3*n^4) := by sorry
