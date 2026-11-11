-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_theorem_2_2
-- name    : FullRankSmallSetQLTC.IndependentChecks.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:37.069958+00:00
-- url     : https://prove2.me/theorems/ddc33de2-0e13-4e7e-8055-11ab07c47155
-- title:
--   Theorem 2.2 — both check matrices of the balanced product have full row rank
-- statement:
--   Let $\Gamma_A=(A_0,A_1,E_A)$ and $\Gamma_B=(B_0,B_1,E_B)$ be bipartite graphs with a common free $G$-action (preserving their edges), with adjacency maps $A:\mathbb F_2^{A_0}\to\mathbb F_2^{A_1}$ and $B:\mathbb F_2^{B_0}\to\mathbb F_2^{B_1}$. If $A$ is injective and $B$ is surjective, then the two parity-check matrices $H_X=(S_0^T\ T_0^T)$ and $H_Z=(T_1\ S_1)$ of the Lin–Hsieh balanced-product code have full row rank:
--   $$\operatorname{rank}H_X=|V_{00}|,\qquad\operatorname{rank}H_Z=|V_{11}|.$$
--
--   Differences from the source:
--   - encoding: bipartite graphs with a common free G-action → finite vertex types with free actions of G on all four classes, preserving the edges; reason: an action on a graph preserves its edges
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Theorem 2.2, p. 12 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_BalancedProduct

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction Matrix

open Classical in
/-- **Theorem 2.2** (Rank inheritance, p. 12). Let `Γ_A = (A₀, A₁, E_A)` and
`Γ_B = (B₀, B₁, E_B)` be bipartite graphs with a common free `G`-action, with adjacency maps
`A : 𝔽₂^{A₀} → 𝔽₂^{A₁}` and `B : 𝔽₂^{B₀} → 𝔽₂^{B₁}`. If `A` is injective and `B` is
surjective, then both parity-check matrices `H_X`, `H_Z` of the Lin–Hsieh balanced-product code
have full row rank. -/
theorem theorem_2_2 (G : Type*) [Group G] {A₀ A₁ B₀ B₁ : Type*}
    [MulAction G A₀] [MulAction G A₁] [MulAction G B₀] [MulAction G B₁]
    [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]
    [DecidableEq A₀] [DecidableEq A₁] [DecidableEq B₀] [DecidableEq B₁]
    (adjA : A₀ → A₁ → Prop) [DecidableRel adjA] (adjB : B₀ → B₁ → Prop) [DecidableRel adjB]
    (hA₀ : IsFreeAction G A₀) (hA₁ : IsFreeAction G A₁)
    (hB₀ : IsFreeAction G B₀) (hB₁ : IsFreeAction G B₁)
    (hA : IsInvariantRel G adjA) (hB : IsInvariantRel G adjB)
    (hinj : Function.Injective (adjMatrix adjA).mulVec)
    (hsurj : Function.Surjective (adjMatrix adjB).mulVec) :
    (bpHX G adjA adjB).rank = Fintype.card (BPVert G A₀ B₀) ∧
    (bpHZ G adjA adjB).rank = Fintype.card (BPVert G A₁ B₁) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
