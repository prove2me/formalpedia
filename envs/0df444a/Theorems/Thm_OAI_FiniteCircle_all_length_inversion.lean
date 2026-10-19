-- Prove2me | Theorems.Thm_OAI_FiniteCircle_all_length_inversion
-- name    : OAI.FiniteCircle.all_length_inversion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:17:38.706577+00:00
-- url     : https://prove2.me/theorems/6ea315f9-2d1d-4957-a7dc-433607c39458
-- title:
--   Inverting the length cap: $\exp\bigl(\tfrac{1}{8192}\sqrt{\log d\,\log\log d}\bigr)\le(2q)^{4q^4}$ whenever $d<L(2q+2)$
-- statement:
--   For a natural number $n$ define the *length cap*
--   $$L(n)=\bigl(n^{4}\bigr)^{32(n^{4})^{2}}=n^{128n^{8}},$$
--   and for a natural number $d$ define the exponent scale $\sigma(d)=\sqrt{\log d\cdot\log\log d}$, with natural logarithms and with $\sigma(d)=0$ when the product under the root is negative.
--
--   **Theorem.** Let $q\ge500000$ and $d\ge2$ be natural numbers with $d<L(2(q+1))$. Then
--
--   $$
--   \exp\Bigl(\frac{1}{8192}\sqrt{\log d\,\log\log d}\Bigr)\ \le\ (2q)^{4q^{4}}.
--   $$
--
--   The lower bound on the optimal $\ell^1$ distortion of edit distance on words of length at most $d$ is proved by building hard families of words at the parameter $n=2q$, where $q$ is chosen with $L(2q)\le d<L(2q+2)$; their distortion is bounded below by $(2q)^{4q^{4}}$. This inequality converts that bound into the form $\exp\bigl(c\,\sigma(d)\bigr)$ with the explicit constant $c=1/8192$, uniformly for every length $d$ in the range, which is the shape of the lower bound in the main theorem.
--
--   **Formalization Note** In Lean $\sigma(d)$ is `exponentScale d = Real.sqrt (Real.log d * Real.log (Real.log d))`. Since `Real.sqrt` of a negative number is $0$, for $d=2$ (where $\log\log2<0$) the left-hand side equals $1$. The cap is `lowerCap n = (n^4)^(32*(n^4)^2)`, and only the upper inequality $d<L(2(q+1))$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Lower.lean#L95-L112

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.all_length_inversion {q d : ℕ} (hq : 500000≤q) (hd0 : 2≤d)
    (hd : d<lowerCap (2*(q+1))) :
    Real.exp ((1/8192)*exponentScale d) ≤ ((2*q:ℕ):ℝ)^(4*q^4) := by sorry
