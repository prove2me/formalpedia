-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_lemma26_equivalence_invariance
-- name    : MaxLatticeFree.Inequalities.lemma26_equivalence_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:02:57.701694+00:00
-- url     : https://prove2.me/theorems/5a6b00e5-5673-4321-b2f7-f7b72a43c598
-- title:
--   Lemma 26: sublinearity and minimality are invariant under equivalence
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point, and let $C\in\mathbb R^{\ell\times q}$, $d\in\mathbb R^\ell$ with $V=\{x\in f+W\mid Cx=d\}$. Let $\Psi(s)\ge\alpha$ and $\Psi'(s)\ge\alpha'$ be two valid inequalities for $R_f(W)$ that are equivalent: there are $\rho>0$, $\lambda\in\mathbb R^\ell$ with $\psi(r)=\rho\psi'(r)+\lambda^TCr$ for $r\in W$ and $\alpha=\rho\alpha'+\lambda^T(d-Cf)$. Then
--
--   1. $\psi$ is sublinear if and only if $\psi'$ is sublinear;
--   2. $\Psi(s)\ge\alpha$ is dominated by a minimal valid inequality (with right-hand side $\alpha$) if and only if $\Psi'(s)\ge\alpha'$ is dominated by a minimal valid inequality (with right-hand side $\alpha'$);
--   3. $\Psi(s)\ge\alpha$ is minimal if and only if $\Psi'(s)\ge\alpha'$ is minimal.
--
--   This lets the proof of Theorem 3 replace an inequality by any equivalent one, in particular by one with right-hand side $1$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 17, Lemma 26

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

namespace MaxLatticeFree.Inequalities

theorem lemma26_equivalence_invariance {q ℓ : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (ψ ψ' : W → ℝ) (α α' : ℝ)
    (hequiv : Equivalent f W C d ψ α ψ' α') :
    (IsSublinear ψ ↔ IsSublinear ψ') ∧
    ((∃ φ : W → ℝ, IsMinimal f W φ α ∧ Dominates φ ψ) ↔
        (∃ φ' : W → ℝ, IsMinimal f W φ' α' ∧ Dominates φ' ψ')) ∧
    (IsMinimal f W ψ α ↔ IsMinimal f W ψ' α') := by sorry

end MaxLatticeFree.Inequalities
