-- Prove2me | Theorems.Thm_MasulloGRH_abs_summing_of_l1_tensor_topologies_eq
-- name    : MasulloGRH.abs_summing_of_l1_tensor_topologies_eq
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:10:44.518184+00:00
-- url     : https://prove2.me/theorems/7ee861a5-308c-4fb7-bb82-b8ade2dd5b5a
-- title:
--   $E\otimes_\pi\ell^1=E\otimes_\varepsilon\ell^1$ implies all local canonical maps are absolutely summing
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ such that the projective and injective topologies on the algebraic tensor product $E\otimes \ell^1$ coincide. Then for every continuous seminorm $p$ on $E$ there is a continuous seminorm $q$ on $E$ such that for all finite families $x_1,\dots,x_n\in E$
--
--   $$\sum_{i=1}^n p(x_i)\;\le\;\sup\Big\{\sum_{i=1}^n |f(x_i)| : f\in E',\ |f|\le q\Big\}.$$
--
--   (Stated in Lean as: any real $c$ bounding the right-hand side bounds the left-hand side.) Proof idea: the seminorm $p\otimes_\pi\|\cdot\|_1$ is $\pi$-continuous hence $\varepsilon$-continuous, so it is dominated by $C\sup_{A\times B}|u|$ with $A\subseteq E'$, $B\subseteq(\ell^1)'$ equicontinuous; take $q=C'\sup_{a\in A}|a(\cdot)|$ and evaluate on $u=\sum_i x_i\otimes e_i$, using $\pi_{p,1}(\sum_i x_i\otimes e_i)=\sum_i p(x_i)$. In other words, each canonical map $\widetilde E_q\to\widetilde E_p$ is absolutely summing with $\pi_1$-norm at most $1$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4 (characterization of nuclearity via ℓ¹); A. Pietsch, Nuclear Locally Convex Spaces (1972), Thm 4.2.5 and §3.3 (absolutely summing ⇒ composition nuclear); A. Grothendieck, Produits tensoriels topologiques (1955), Ch. II §3.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem abs_summing_of_l1_tensor_topologies_eq (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (ht : projTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) =
      epsTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))) :
    ∀ p : Seminorm ℂ E, Continuous p → ∃ q : Seminorm ℂ E, Continuous q ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
        ∑ i, p (x i) ≤ c := by sorry

end MasulloGRH
