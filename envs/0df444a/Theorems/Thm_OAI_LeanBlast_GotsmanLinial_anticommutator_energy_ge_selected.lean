-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_anticommutator_energy_ge_selected
-- name    : OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:55:14.49798+00:00
-- url     : https://prove2.me/theorems/42dfb739-55a9-4589-9397-d68c2eef048a
-- title:
--   Anticommutator with a sign diagonal captures four times the diagonal and equal-sign neighbor mass
-- statement:
--   Let $\iota$ be a finite index set and $\rho:\iota\times\iota\to\mathbb{N}$ a function such that $\rho(i,j)=0$ implies $i=j$; for $k\in\mathbb{N}$ let $S_k=\{(i,j):\rho(i,j)=k\}$. Let $M\in\mathbb{C}^{\iota\times\iota}$, let $h:\iota\to\{-1,1\}$ be a sign function with diagonal matrix $H=\operatorname{diag}(h)$, and let $s\subseteq S_1$ be a set of pairs at distance one along which $h$ is constant, i.e. $h(i)=h(j)$ for every $(i,j)\in s$. Then
--
--   $$
--   4\Bigl(\sum_{(i,j)\in S_0}|M_{ij}|^2+\sum_{(i,j)\in s}|M_{ij}|^2\Bigr)\;\le\;\bigl\|MH+HM\bigr\|_{\mathrm{HS}}^2,
--   $$
--
--   where $\|A\|_{\mathrm{HS}}^2=\sum_{i,j}|A_{ij}|^2$.
--
--   The anticommutator $MH+HM$ has entries $(h(i)+h(j))\,M_{ij}$, so it doubles the entries joining equal signs and annihilates those joining opposite signs. The lemma turns the mass of $M$ on the distance-zero pairs and on selected equal-sign edges into a lower bound for the anticommutator energy; in the Gotsman–Linial argument the selected edges are the constant-sign edges of the parity-twisted threshold function.
--
--   **Formalization Note** $\rho$ is given in curried form, $h$ is a real function taking only the values $1$ and $-1$, $H$ is the complex diagonal matrix with entries $h(i)$, and $S_k$ is `distanceShell` applied to $(i,j)\mapsto\rho(i,j)$. The squared norm is the explicit entry sum `hsNormSq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean#L107-L148

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2) :
    4 * ((∑ p ∈ distanceShell (fun p : ι × ι => ρ p.1 p.2) 0,
        ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) ≤
      hsNormSq (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by sorry
