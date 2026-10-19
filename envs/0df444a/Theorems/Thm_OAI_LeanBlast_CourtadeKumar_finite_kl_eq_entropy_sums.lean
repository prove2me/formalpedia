-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_finite_kl_eq_entropy_sums
-- name    : OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:53:39.823261+00:00
-- url     : https://prove2.me/theorems/f25f6600-3fb5-4a1e-952a-ae20934369e6
-- title:
--   Mutual information of a finite nonnegative array as a combination of $t\log t$ sums
-- statement:
--   Let $A,B$ be finite sets and $j:A\times B\to[0,\infty)$. Write $r_a=\sum_bj(a,b)$ and $c_b=\sum_aj(a,b)$ for the row and column sums, and $\phi(t)=t\log t$. Then
--   $$
--   \sum_{a,b:\ j(a,b)>0}j(a,b)\log\frac{j(a,b)}{r_a\,c_b}=\sum_{a,b}\phi\bigl(j(a,b)\bigr)-\sum_a\phi(r_a)-\sum_b\phi(c_b).
--   $$
--
--   For a joint probability table $j$, the left side is the mutual information between the two coordinates. The identity expresses it through the entropies of the joint law and of the two marginals, which is the form used to analyse the Courtade–Kumar mutual information.
--
--   **Formalization Note** No normalization of $j$ is assumed, and terms with $j=0$ on the left are omitted. Lean's $\log0=0$ makes $\phi(0)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/FiniteInformation.lean#L22-L55

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
universe u v

theorem OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (j : A → B → ℝ) (hj : ∀ a b, 0 ≤ j a b) :
    (∑ a : A, ∑ b : B,
      if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      (∑ a : A, ∑ b : B, xlogx (j a b)) -
        (∑ a : A, xlogx (∑ b : B, j a b)) -
        (∑ b : B, xlogx (∑ a : A, j a b)) := by sorry
