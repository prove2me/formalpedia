-- Prove2me | Theorems.Thm_HryniewiczCriterion_graphUnitary4_positive_path
-- name    : HryniewiczCriterion.graphUnitary4_positive_path
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:36:33.743976+00:00
-- url     : https://prove2.me/theorems/756dfa1a-c1ec-4f1e-b0d6-6ed576b51c79
-- title:
--   The graph unitary of a positive symplectic path is a positive unitary path
-- statement:
--   Let $\hat Y:\mathbb{R}\to\mathbb{R}^{4\times4}$ solve $\hat Y'=J\,S(t)\,\hat Y$ with $\hat Y(0)=I$, where every $S(t)$ is symmetric positive definite and $J$ is the standard complex structure in the coordinates $(q_1,p_1,q_2,p_2)$. Let $V(t)=W(\Gamma_{\hat Y(t)})\,W(\Delta)^{-1}$ be the graph unitary (`graphUnitary4`). Then $V(0)=I$, every $V(t)$ is unitary, and $V$ is a positive path:
--   $$V'(t)=i\,Q(t)\,V(t)\qquad\text{with } Q(t) \text{ Hermitian positive definite.}$$
--   Proof idea: $\hat Y(t)$ is symplectic, so $\Gamma_{\hat Y(t)}$ is Lagrangian in $(\mathbb{R}^4\oplus\mathbb{R}^4,-\omega_0\oplus\omega_0)$ and $V(t)$ is unitary. For a unitary frame $U$ of a Lagrangian path, $U^*U'=R+iP$ with $R$ real antisymmetric and $P$ the crossing form, so $(UU^{\mathsf T})'=2i\,(UPU^*)\,UU^{\mathsf T}$. On the graph the crossing form is $(z,\hat Yz)\mapsto\omega_0(\hat Yz,JS\hat Yz)=\langle S\hat Yz,\hat Yz\rangle>0$.
-- source:
--   Positivity of the crossing form of the graph of a positive symplectic path; Robbin–Salamon, The Maslov index for paths, Topology 32 (1993), https://doi.org/10.1016/0040-9383(93)90052-W, Section 1, and the Souriau map $W(L)=UU^{\mathsf T}$ (Arnold). Used in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, (3.43), p. 221.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff ComplexOrder

theorem HryniewiczCriterion.graphUnitary4_positive_path (Ŷ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hSpos : ∀ t, (S t).PosDef) (h0 : Ŷ 0 = 1)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => Ŷ s i j) ((symplJ4 * S t * Ŷ t) i j) t) :
    graphUnitary4 (Ŷ 0) = 1 ∧ (∀ t, star (graphUnitary4 (Ŷ t)) * graphUnitary4 (Ŷ t) = 1) ∧
      ∃ Q : ℝ → Matrix (Fin 4) (Fin 4) ℂ, ∀ t, (Q t).PosDef ∧
        ∀ i j : Fin 4, HasDerivAt (fun s => graphUnitary4 (Ŷ s) i j)
          ((Complex.I • (Q t * graphUnitary4 (Ŷ t))) i j) t := by sorry
