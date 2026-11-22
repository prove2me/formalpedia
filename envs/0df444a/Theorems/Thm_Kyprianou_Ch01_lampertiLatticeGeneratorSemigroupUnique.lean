-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiLatticeGeneratorSemigroupUnique
-- name    : Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique
-- status  : Proved
-- author  : @coqelz
-- created : 2026-11-22T10:14:56.751804+00:00
-- url     : https://prove2.me/theorems/91f06661-95bf-430e-8cec-cb3e0fcdab98
-- title:
--   Uniqueness of the PMF semigroup with the bounded lattice compound-Poisson generator
-- statement:
--   Fix $\lambda\ge0$ and an offspring law $(p_k)$ on $\mathbb N$ with $p_1=0$. Let $K^{(1)},K^{(2)}$ be two families of PMFs $K_z(t)$ on $\mathbb N$ ($z\in\mathbb N$, $t\ge0$). Suppose each satisfies the Chapman–Kolmogorov equation $K_z(s+t)=\sum_n K_z(s)(n)K_n(t)$ and $K_z(0)=\delta_z$, and that for every $z,k$ the map $t\mapsto K_z(t)(k)$ has right derivative at $t=0$ equal to
--   $$g(z,k)=\begin{cases}0 & z=0,\\ -\lambda & k=z\ge 1,\\ \lambda\,p_{k+1-z} & z\ge 1,\ k\ne z,\ k\ge z-1,\\ 0 & \text{otherwise},\end{cases}$$
--   Then $K^{(1)}=K^{(2)}$.
--
--   The generator's rows are bounded in $\ell^1$ by $2\lambda$, so the transition function is determined by its $q$-matrix. It is the uniformly continuous semigroup $e^{tG}$. Equivalently, the Kolmogorov backward equation $\partial_t K=GK$ has a unique bounded solution (Reuter's uniqueness theorem for bounded $q$-matrices).
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26; sub-lemma of the forward Lamperti finite-dimensional law target 45b13ab4-970c-4134-a679-c62b276b5f42.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiLatticeGeneratorSemigroupUnique
    (rate : ℝ≥0) (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ z : ℕ, K₁ z 0 = PMF.pure z)
    (hInit₂ : ∀ z : ℕ, K₂ z 0 = PMF.pure z)
    (hGen₁ : ∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((K₁ z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0)
    (hGen₂ : ∀ z k : ℕ,
        HasDerivWithinAt
          (fun t : ℝ => ((K₂ z (Real.toNNReal t)) k).toReal)
          (if k = z then (if z = 0 then 0 else -(rate : ℝ))
           else if 1 ≤ z ∧ z ≤ k + 1 then
             (rate : ℝ) * (offspring (k + 1 - z)).toReal
           else 0)
          (Set.Ici 0) 0) :
    K₁ = K₂ := by sorry
