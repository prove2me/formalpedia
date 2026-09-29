-- Prove2me | Theorems.Thm_HeckeCohomology_heckeH1_delta0
-- name    : HeckeCohomology.heckeH1_delta0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9b3fe1c4-144e-591d-8e8d-0e1dcef8cd46
-- title:
--   Transfer Hecke operators commute with the connecting map H⁰ → H¹
-- statement:
--   Let $k$ be a commutative ring and $\Gamma$ a group, let $S_1, S_2 \le \Gamma$ be subgroups with $S_2$ of finite index, and let $c : S_2 \to S_1$ be a group homomorphism. Let $X$ be a short complex $X_1 \to X_2 \to X_3$ in $\mathrm{Rep}\,k\,\Gamma$ together with a proof `hX` that it is short exact. Suppose given $k$-linear endomorphisms $\varphi_i$ of $X_i$ ($i = 1,2,3$), each a twist in the sense that $\varphi_i(\rho(c(s))a) = \rho(s)(\varphi_i a)$ for all $s \in S_2$ and all $a$, and suppose the $\varphi_i$ are compatible with the two maps of $X$: $f(\varphi_1 a) = \varphi_2(f a)$ for all $a \in X_1$ and $g(\varphi_2 b) = \varphi_3(g b)$ for all $b \in X_2$. Then for every $\Gamma$-invariant $z \in X_3$ the two composites agree: applying the connecting map $\delta : H^0(\Gamma, X_3) \to H^1(\Gamma, X_1)$ of `hX` to the class of $z$ and then the operator `heckeH1` on $H^1(\Gamma, X_1)$ attached to $\varphi_1$ gives the same element as first applying `heckeInv` — the restriction to invariants of $a \mapsto \sum_q \rho(\mathrm{rep}(q))^{-1}(\varphi_3 a)$, the sum being over the right cosets of $S_2$ — and then $\delta$. Here $H^0$ is identified with the invariants via `H0Iso`.
--
--   This is the compatibility of transfer-type (Hecke) operators with the degree-zero connecting homomorphism of a short exact sequence of coefficients, i.e. commutativity of the square relating the norm operator on invariants and the induced operator on $H^1$. It is used in the construction of eigenvectors for such operators on $H^1$ along a short exact sequence, in [`HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact`](thm.html#HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_heckeH1_delta0.lean

import Definitions.Def_GroupCohomology_TransferHecke
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology in

theorem HeckeCohomology.heckeH1_delta0 {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) [S₂.FiniteIndex]
    {X : ShortComplex (Rep k Γ)} (hX : X.ShortExact)
    (φ₁ : X.X₁ →ₗ[k] X.X₁) (hφ₁ : IsTwist S₁ S₂ c X.X₁ φ₁)
    (φ₂ : X.X₂ →ₗ[k] X.X₂) (hφ₂ : IsTwist S₁ S₂ c X.X₂ φ₂)
    (φ₃ : X.X₃ →ₗ[k] X.X₃) (hφ₃ : IsTwist S₁ S₂ c X.X₃ φ₃)
    (hf : ∀ a : X.X₁, X.f.hom (φ₁ a) = φ₂ (X.f.hom a))
    (hg : ∀ b : X.X₂, X.g.hom (φ₂ b) = φ₃ (X.g.hom b))
    (z : X.X₃.ρ.invariants) :
    heckeH1 S₁ S₂ c X.X₁ φ₁ hφ₁ (δ hX 0 1 rfl ((H0Iso X.X₃).inv z)) =
      δ hX 0 1 rfl ((H0Iso X.X₃).inv (heckeInv S₁ S₂ c X.X₃ φ₃ hφ₃ z)) := by sorry
