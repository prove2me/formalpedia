-- Prove2me | Theorems.Thm_HeckeCohomology_heckeH1_eq_of_section
-- name    : HeckeCohomology.heckeH1_eq_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0384deaf-48e7-56d5-937a-fc30d132a83d
-- title:
--   Transfer Hecke operator on H¹ is independent of the cross-section
-- statement:
--   Let $k$ be a commutative ring, $\Gamma$ a group, $S_1,S_2\le\Gamma$ with $S_2$ of finite index, $c\colon S_2\to S_1$ a group homomorphism, and $A$ a $k$-linear representation of $\Gamma$. Let $\varphi\colon A\to A$ be $k$-linear and satisfy `IsTwist`, i.e. $\varphi(\rho_A(c(s))a)=\rho_A(s)\varphi(a)$ for all $s\in S_2$ and $a\in A$. Write $Q$ for the quotient of $\Gamma$ by the right-coset relation of $S_2$ and `cls` for the canonical map $\Gamma\to Q$. Let $r\colon Q\to\Gamma$ be any map and $\sigma\colon Q\to\Gamma\to S_2$ be such that for all $q\in Q$ and $\gamma\in\Gamma$ the element $\sigma(q,\gamma)$ of $S_2$ equals, in $\Gamma$, $r(q)\,\gamma\,r(\mathrm{cls}(r(q)\gamma))^{-1}$; in particular $r$ is forced to be a cross-section of $Q$. Finally let $f,g$ be inhomogeneous $1$-cocycles of $\Gamma$ on $A$ with $g(\gamma)=\sum_{q\in Q}\rho_A(r(q)^{-1})\bigl(\varphi(f(c(\sigma(q,\gamma))))\bigr)$ for every $\gamma\in\Gamma$, the sum being finite since $[\Gamma:S_2]<\infty$. Then the class of $g$ in $H^1(\Gamma,A)$ equals the image of the class of $f$ under `heckeH1`, the $k$-linear endomorphism of $H^1$ induced by the cocycle-level transfer operator `heckeZ1` built from the canonical choice of coset representatives.
--
--   This is the independence of the transfer (corestriction-type) Hecke operator on $H^1$ from the choice of right-coset cross-section: any cocycle whose values are the transfer sums formed with an arbitrary cross-section $r$ represents the canonical Hecke image. It is used when verifying that Hecke operators attached to various twisting data commute with one another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_heckeH1_eq_of_section.lean

import Definitions.Def_GroupCohomology_TransferHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
open groupCohomology in

theorem HeckeCohomology.heckeH1_eq_of_section {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ) [S₂.FiniteIndex]
    (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ)
    (r : Quotient (QuotientGroup.rightRel S₂) → Γ)
    (σ : Quotient (QuotientGroup.rightRel S₂) → Γ → S₂)
    (hσ : ∀ q γ, (σ q γ : Γ) = r q * γ * (r (cls S₂ (r q * γ)))⁻¹)
    (f g : cocycles₁ A)
    (hg : ∀ γ : Γ, g γ = ∑ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (r q)⁻¹ (φ (f (c (σ q γ) : Γ)))) :
    H1π A g = heckeH1 S₁ S₂ c A φ hφ (H1π A f) := by sorry
