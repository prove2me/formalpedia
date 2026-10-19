-- Prove2me | Theorems.Thm_OAI_FiniteCircle_finite_partition
-- name    : OAI.FiniteCircle.finite_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:20:47.386091+00:00
-- url     : https://prove2.me/theorems/4fb78a21-5c5f-49c2-9ab0-a966030074e4
-- title:
--   Random partitions with collision probability $e^{-\alpha\rho(x,y)}$ for cut-decomposable distances
-- statement:
--   Let $X$ be a finite set. A *cut* of $X$ is a map $c:X\to\{0,1\}$, with cut distance $\delta_c(x,y)=1$ if $c(x)\ne c(y)$ and $\delta_c(x,y)=0$ otherwise. A function $\rho:X\times X\to\mathbb{R}$ has a *cut representation* if there are coefficients $a_c\ge0$, one for each of the $2^{|X|}$ cuts $c$, such that
--   $$\rho(x,y)=\sum_{c:X\to\{0,1\}}a_c\,\delta_c(x,y)\qquad\text{for all }x,y\in X.$$
--   (Nonnegative combinations of cut distances form the cut cone; on a finite set these are exactly the semimetrics that embed isometrically into $\ell^1$.) Let $\mathcal P=\{0,1\}^{\{0,1\}^{X}}$ be the finite set of maps from cuts to bits. A finite probability law on $\mathcal P$ is a nonnegative weight function on $\mathcal P$ with total weight $1$.
--
--   **Theorem.** Suppose that $\rho$ has a cut representation and that $\alpha\ge0$ is real. Then there exist a finite probability law $\mu$ on $\mathcal P$ and a labelling map $(\omega,x)\mapsto\operatorname{label}_\omega(x)$ from $\mathcal P\times X$ to $\mathcal P$ such that for all $x,y\in X$
--
--   $$
--   \mu\bigl\{\omega\in\mathcal P:\ \operatorname{label}_\omega(x)=\operatorname{label}_\omega(y)\bigr\}=e^{-\alpha\,\rho(x,y)}.
--   $$
--
--   Each outcome $\omega$ partitions $X$ into the fibres of $\operatorname{label}_\omega$, so this is a random partition of $X$ in which two points fall into the same part with probability exactly $e^{-\alpha\rho(x,y)}$; in particular they are separated with probability $1-e^{-\alpha\rho(x,y)}\le\alpha\rho(x,y)$. In the recursive $\ell^1$ embedding of edit distance it is applied with $\rho$ the $\ell^1$ distance of an existing embedding of shorter words (which always has a cut representation) and with rates $\alpha$ adapted to dyadic window scales; histograms of the resulting labels form the coordinates of the next embedding.
--
--   **Formalization Note** The outcome space is `PartitionSpace X = (X → Bool) → Bool`, the law is a `FiniteLaw`, and the probability is `μ.event`. The statement is wrapped in `classical` so that equality of labels is decidable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Partitions.lean#L151-L180

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.finite_partition {X : Type*} [Fintype X] {ρ : X → X → ℝ}
    (hρ : HasCutRepresentation ρ) (α : ℝ) (hα : 0 ≤ α) : by
  classical
  exact ∃ (μ : FiniteLaw (PartitionSpace X)) (label : PartitionSpace X → X → PartitionSpace X),
      ∀ x y, μ.event (fun ω => label ω x = label ω y) = Real.exp (-α * ρ x y) := by sorry
