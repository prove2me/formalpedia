-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_minimal_valid_inequalities_characterization
-- name    : MaxLatticeFree.Inequalities.minimal_valid_inequalities_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:23:48.437299+00:00
-- url     : https://prove2.me/theorems/4e35fc1a-abdf-4f99-8adb-744704443442
-- title:
--   Theorem 3: minimal valid inequalities for $R_f(W)$ come from maximal lattice-free convex sets
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point, let $V$ be the affine hull of $(f+W)\cap\mathbb Z^q$, and let $C\in\mathbb R^{\ell\times q}$, $d\in\mathbb R^\ell$ with $V=\{x\in f+W\mid Cx=d\}$.
--
--   1. Every nontrivial valid linear inequality $\sum_{r\in W}\psi(r)s_r\ge\alpha$ for $R_f(W)$ is dominated by a nontrivial minimal valid linear inequality $\sum_{r\in W}\psi'(r)s_r\ge\alpha$ for $R_f(W)$.
--   2. Every nontrivial minimal valid linear inequality $\sum_{r\in W}\psi(r)s_r\ge\alpha$ for $R_f(W)$ is equivalent to an inequality of the form
--   $$\sum_{r\in W}\psi_B(r)s_r\ \ge\ 1$$
--   such that $\psi_B(r)\ge0$ for all $r\in W$ and $B$ is a maximal lattice-free convex set in $f+W$ with $f$ in its interior.
--
--   Here $\psi:W\to\mathbb R$ is an arbitrary function, "trivial" means satisfied by all nonnegative $s\in\mathcal V$, and equivalence is with respect to $C,d$ (Definition 25). The theorem extends the correspondence between irredundant cuts and maximal lattice-free convex sets from rational data to arbitrary real $f$ and $W$.
--
--   **Formalization Note** $\psi_B$ is defined as $\rho_{B-f}$, which equals $\max_i a_ir$ for every tight description $B=\{x\in f+W\mid a_i(x-f)\le1\}$ (Remark 29). The interior of $B$ is relative to $f+W$. The equivalence notion does not depend on which pair $(C,d)$ describing $V$ is chosen.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 6, Theorem 3

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem minimal_valid_inequalities_characterization {q ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (hCd : IsAffineHullDescription f W C d) :
    (∀ (ψ : W → ℝ) (α : ℝ), IsValid f W ψ α → ¬ IsTrivial f W ψ α →
        ∃ ψ' : W → ℝ, IsMinimal f W ψ' α ∧ ¬ IsTrivial f W ψ' α ∧ Dominates ψ' ψ) ∧
    (∀ (ψ : W → ℝ) (α : ℝ), IsMinimal f W ψ α → ¬ IsTrivial f W ψ α →
        ∃ B : Set (EuclideanSpace ℝ (Fin q)), IsMaximalLatticeFree f W B ∧ f ∈ intRel (affSpace f W) B ∧
          (∀ r : W, 0 ≤ psiB f W B r) ∧ Equivalent f W C d ψ α (psiB f W B) 1) := by sorry

end MaxLatticeFree.Inequalities
