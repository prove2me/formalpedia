-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_Supplement_lemma32_linVal_continuous_normH
-- name    : MaxLatticeFree.Geometry.Supplement.lemma32_linVal_continuous_normH
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:02:17.692874+00:00
-- url     : https://prove2.me/theorems/a8236615-e487-4d74-b93b-6276da652e03
-- title:
--   Lemma 32 — Ψ(s) = ∑ ψ(r)s_r is continuous in ‖·‖_H for continuous positively homogeneous ψ
-- statement:
--   Let $W\subseteq\mathbb R^q$ be a linear subspace, $\mathcal W$ the space of finitely supported functions $s:W\to\mathbb R$ with the norm $\|s\|_H=|s_0|+\sum_{r\ne0}\|r\|\,|s_r|$, and let $\psi:W\to\mathbb R$ be continuous and positively homogeneous ($\psi(\lambda r)=\lambda\psi(r)$ for $\lambda\ge0$). Then the linear function
--
--   $$
--   \Psi(s)=\sum_{r\in W}\psi(r)s_r
--   $$
--
--   is continuous on $(\mathcal W,\|\cdot\|_H)$: for every $s\in\mathcal W$ and $\varepsilon>0$ there is $\delta>0$ with $|\Psi(s')-\Psi(s)|<\varepsilon$ whenever $\|s'-s\|_H<\delta$.
--
--   This lemma gives the inclusion "$\subseteq$" of Theorem 4: the half-spaces cut out by the inequalities $\sum\psi_B(r)s_r\ge1$ and the affine subspace $\mathcal V$ are closed in $\|\cdot\|_H$.
--
--   **Formalization Note** No convexity, sublinearity or validity of $\psi$ is assumed. Continuity of $\psi$ is for the topology $W$ inherits from $\mathbb R^q$; positive homogeneity includes $\lambda=0$, so $\psi(0)=0$.
--
--   Differences from the source:
--   - encoding: Ψ is continuous with respect to (𝒲, ‖·‖_H) → ε–δ continuity of linVal ψ at every s, measured by normH (s' − s); reason: the metric of the norm ‖·‖_H; the same statement
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 22, Lemma 32

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_NormH

open MaxLatticeFree.Inequalities

namespace MaxLatticeFree.Geometry.Supplement

theorem lemma32_linVal_continuous_normH {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (hcont : Continuous ψ) (hhom : IsPositivelyHomogeneous ψ) :
    ∀ s : W →₀ ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s' : W →₀ ℝ, normH (s' - s) < δ → |linVal ψ s' - linVal ψ s| < ε := by sorry

end MaxLatticeFree.Geometry.Supplement
