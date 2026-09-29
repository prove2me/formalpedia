-- Prove2me | Theorems.Thm_HeckeCohomology_heckeH1_natural
-- name    : HeckeCohomology.heckeH1_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4918b719-2ffb-5b12-89e6-f8370c300532
-- title:
--   Naturality of the transfer Hecke operator on H¹
-- statement:
--   Fix a commutative ring $k$ and a group $\Gamma$, two subgroups $S_1, S_2 \le \Gamma$ with $S_2$ of finite index, and a group homomorphism $c : S_2 \to S_1$. Let $A$ and $B$ be representations of $\Gamma$ over $k$ and $f : A \to B$ a morphism of such representations. Let $\varphi_A$ be a $k$-linear endomorphism of $A$ which is a twist in the sense of `IsTwist`, i.e. $\varphi_A(\rho_A(c(s))\,a) = \rho_A(s)\,\varphi_A(a)$ for all $s \in S_2$ and $a \in A$, and likewise let $\varphi_B$ be a $k$-linear endomorphism of $B$ satisfying $\varphi_B(\rho_B(c(s))\,b) = \rho_B(s)\,\varphi_B(b)$ for all $s \in S_2$, $b \in B$. Assume $f$ intertwines the two twists: $f(\varphi_A(a)) = \varphi_B(f(a))$ for all $a \in A$. Then for every class $x \in H^1(\Gamma, A)$ the operator `heckeH1` attached to $(S_1, S_2, c, \varphi_B)$ — the $k$-linear endomorphism of $H^1(\Gamma,B)$ obtained by descending the cocycle-level operator `heckeZ1` along the surjection `H1π` from $1$-cocycles onto $H^1$, whose kernel it preserves — applied to the image of $x$ under the degree-one map $H^1(\Gamma,A) \to H^1(\Gamma,B)$ induced by $f$ and the identity of $\Gamma$, coincides with the image under that induced map of the corresponding operator attached to $(S_1, S_2, c, \varphi_A)$ applied to $x$.
--
--   This is the functoriality, in the coefficient representation, of the transfer (corestriction-type) Hecke operator on first group cohomology: such operators form a natural transformation of the functor $H^1(\Gamma, -)$ restricted to representations equipped with compatible twists. It is used in the arguments producing Hecke eigenvectors in $H^1$ from eigenvectors in the cohomology of the terms of a short exact sequence of representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_heckeH1_natural.lean

import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology in

theorem HeckeCohomology.heckeH1_natural {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) {A B : Rep k Γ} [S₂.FiniteIndex] (f : A ⟶ B)
    (φA : A →ₗ[k] A) (hφA : IsTwist S₁ S₂ c A φA)
    (φB : B →ₗ[k] B) (hφB : IsTwist S₁ S₂ c B φB)
    (hcomm : ∀ a : A, f.hom (φA a) = φB (f.hom a)) (x : H1 A) :
    heckeH1 S₁ S₂ c B φB hφB (map (MonoidHom.id Γ) f 1 x) =
      map (MonoidHom.id Γ) f 1 (heckeH1 S₁ S₂ c A φA hφA x) := by sorry
