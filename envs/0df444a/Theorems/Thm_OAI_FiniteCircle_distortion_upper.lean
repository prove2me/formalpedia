-- Prove2me | Theorems.Thm_OAI_FiniteCircle_distortion_upper
-- name    : OAI.FiniteCircle.distortion_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:54:48.733735+00:00
-- url     : https://prove2.me/theorems/8f0868e7-2234-474c-96c9-b327ebc5e45b
-- title:
--   Two-sided Lipschitz bounds give an injective $\ell_1$ embedding with distortion at most $AB$
-- statement:
--   Let $\alpha$ be an alphabet, let $X$ be a set with at least two elements, and let $\mathrm{word}\colon X\to\alpha^*$ be an injective map into the finite words over $\alpha$. Distances on $X$ are measured by the edit distance $\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))$, the least number of single-letter insertions, deletions and substitutions turning $\mathrm{word}(x)$ into $\mathrm{word}(y)$. Let $\ell_1=\ell_1(\mathbb N)$ be the Banach space of absolutely summable real sequences with norm $\|a\|_1=\sum_i|a_i|$. The *distortion* of a map $f\colon X\to\ell_1$ is
--   $$\operatorname{dist}(f)=\Bigl(\sup_{x\neq y}\frac{\|f(x)-f(y)\|_1}{\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))}\Bigr)\cdot\Bigl(\sup_{x\neq y}\frac{\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))}{\|f(x)-f(y)\|_1}\Bigr).$$
--
--   Let $A,B$ be real numbers with $A\ge 0$ and suppose that for all $x,y\in X$
--   $$\|f(x)-f(y)\|_1\le A\cdot\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))\qquad\text{and}\qquad\operatorname{ed}(\mathrm{word}(x),\mathrm{word}(y))\le B\cdot\|f(x)-f(y)\|_1 .$$
--   Then
--
--   $$
--   f\ \text{is injective}\qquad\text{and}\qquad\operatorname{dist}(f)\le A\,B .
--   $$
--
--   This is the standard way to certify an upper bound on the optimal $\ell_1$ distortion of a set of words: an embedding that expands edit distances by at most a factor $A$ and contracts them by at most a factor $B$ is admissible (injective) and has distortion at most $AB$. It is used to derive the upper bound on the optimal distortion of all words of length at most $d$ from an explicit two-sided embedding.
--
--   **Formalization Note** The two suprema are Lean's `sSup` on $\mathbb R$ of the sets of ratios over ordered pairs $x\neq y$ (`upperRates`, `lowerRates`), so no finiteness of $X$ is needed; the hypotheses supply the upper bounds. The space $\ell_1$ is `RealL1 = lp (fun _ : ℕ => ℝ) 1`, and "at least two elements" is the instance `Nontrivial X`. No sign condition on $B$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Distortion.lean#L100-L131

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

theorem OAI.FiniteCircle.distortion_upper {α X : Type*} [Nontrivial X]
    (word : X → List α) (hw : Function.Injective word)
    (f : X → RealL1) (A B : ℝ) (hA : 0≤A)
    (hu : ∀ x y, ‖f x-f y‖ ≤ A*(editDistance (word x) (word y):ℝ))
    (hl : ∀ x y, (editDistance (word x) (word y):ℝ) ≤ B*‖f x-f y‖) :
    Function.Injective f ∧ distortion word f ≤ A*B := by sorry
