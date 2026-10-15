-- Prove2me | Theorems.Thm_OAI_DiscreteFree_opposing_pairing_lower
-- name    : OAI.DiscreteFree.opposing_pairing_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:52:55.33241+00:00
-- url     : https://prove2.me/theorems/48fafb7c-8135-4f1e-89a4-ceeaaf8e8c43
-- title:
--   Lower bound for a difference of pairings against a test function carrying opposite bumps
-- statement:
--   Let $S$ be a finite set. For $\mu,f\colon S\to\mathbb{R}$ write
--   $$
--   \langle\mu,f\rangle=\sum_{j\in S}\mu_j f_j,\qquad \operatorname{var}_E(\mu)=\sum_{j\in E}|\mu_j|\quad(E\subseteq S)
--   $$
--   for the pairing and for the variation of $\mu$ on $E$.
--
--   **Theorem.** Let $\mu,\nu,f,b,c\colon S\to\mathbb{R}$, let $E,F\subseteq S$ and $L\in\mathbb{R}$, and assume that for every $j\in S$
--   $$
--   |f_j|\le L,\qquad 0\le b_j\le L,\qquad 0\le c_j\le L,
--   $$
--   that $f_j=b_j$ for every $j\notin E$, and that $f_j=-c_j$ for every $j\notin F$. Then
--   $$
--   \langle\mu,b\rangle+\langle\nu,c\rangle-2L\bigl(\operatorname{var}_E(\mu)+\operatorname{var}_F(\nu)\bigr)\ \le\ \langle\mu,f\rangle-\langle\nu,f\rangle .
--   $$
--
--   The test vector $f$ looks like the nonnegative bump $b$ to $\mu$ and like the nonpositive bump $-c$ to $\nu$, except on the exceptional sets $E$ and $F$; the inequality says that the two bump masses survive in the difference of pairings up to an error proportional to the mass of $\mu$ and $\nu$ on the exceptional sets. In the finite-rank obstruction, $\mu$ and $\nu$ are the coefficient vectors of the images under an operator of two point evaluations at adjacent vertices, and this lower bound is played against the upper bound coming from the operator norm.
--
--   **Formalization Note** The pairing and the variation are `pairing μ f` and `variationOn μ E` (the latter a sum over the finite type of $|\mu_j|$ restricted to $E$ by an indicator); $E$ and $F$ are arbitrary subsets of the finite type $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SignedTests.lean#L72-L93

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
variable {S : Type*} [Fintype S]

theorem OAI.DiscreteFree.opposing_pairing_lower (μ ν f b c : S → ℝ) (E F : Set S) (L : ℝ)
    (hf : ∀ j, |f j| ≤ L)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (he : ∀ j, j ∉ E → f j = b j)
    (hF : ∀ j, j ∉ F → f j = -c j) :
    pairing μ b + pairing ν c - 2 * L * (variationOn μ E + variationOn ν F) ≤
      pairing μ f - pairing ν f := by sorry
