-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_2_1
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:49.004424+00:00
-- url     : https://prove2.me/theorems/58fd86ae-6c96-49c1-ab84-6849d3e5abad
-- title:
--   Lemma 2.1 — directional maps are direct sums of input adjacency maps
-- statement:
--   Let $\Gamma_A=(A_0,A_1,E_A)$ and $\Gamma_B=(B_0,B_1,E_B)$ be finite bipartite graphs with a common free $G$-action preserving their edges, with adjacency maps $A$ and $B$. In their balanced product, the subgraph between $V_{00}$ and $V_{10}$ defined by $S_0$ is a disjoint union of $|B_0/G|$ copies of $\Gamma_A$; equivalently, after suitable orderings of the bases,
--   $$S_0\cong\bigoplus_{B_0/G}A .$$
--   Likewise $S_1\cong\bigoplus_{B_1/G}A$, $T_0\cong\bigoplus_{A_0/G}B$ and $T_1\cong\bigoplus_{A_1/G}B$.
--
--   Differences from the source:
--   - encoding: after suitable orderings of the bases, S₀ ≅ ⊕_{B₀/G} A (equivalently, a disjoint union of |B₀/G| copies of Γ_A) → there are bijections V₀₀ ≃ A₀ × B₀/G and V₁₀ ≃ A₁ × B₀/G under which S₀ becomes the block-diagonal matrix with one block A per orbit of B₀; reason: this is the matrix form the source gives as equivalent
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 2.1, p. 11 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_BalancedProduct

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction Matrix

open Classical in
/-- **Lemma 2.1** ([LH22, Lemma 26], p. 11). For two bipartite graphs `Γ_A`, `Γ_B` with a
common free `G`-action preserving their edges, after suitable orderings of the bases each
directional map of the balanced product is a direct sum of copies of an input adjacency map:
`S₀ ≅ ⊕_{B₀/G} A`, `S₁ ≅ ⊕_{B₁/G} A`, `T₀ ≅ ⊕_{A₀/G} B`, `T₁ ≅ ⊕_{A₁/G} B`. -/
theorem lemma_2_1 (G : Type*) [Group G] {A₀ A₁ B₀ B₁ : Type*}
    [MulAction G A₀] [MulAction G A₁] [MulAction G B₀] [MulAction G B₁]
    [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]
    [DecidableEq A₀] [DecidableEq A₁] [DecidableEq B₀] [DecidableEq B₁]
    (adjA : A₀ → A₁ → Prop) [DecidableRel adjA] (adjB : B₀ → B₁ → Prop) [DecidableRel adjB]
    (hA₀ : IsFreeAction G A₀) (hA₁ : IsFreeAction G A₁)
    (hB₀ : IsFreeAction G B₀) (hB₁ : IsFreeAction G B₁)
    (hA : IsInvariantRel G adjA) (hB : IsInvariantRel G adjB) :
    (∃ (e₀ : BPVert G A₀ B₀ ≃ A₀ × orbitRel.Quotient G B₀)
        (e₁ : BPVert G A₁ B₀ ≃ A₁ × orbitRel.Quotient G B₀),
        (Smap G adjA B₀).submatrix e₁.symm e₀.symm = blockDiagonal fun _ => adjMatrix adjA) ∧
    (∃ (e₀ : BPVert G A₀ B₁ ≃ A₀ × orbitRel.Quotient G B₁)
        (e₁ : BPVert G A₁ B₁ ≃ A₁ × orbitRel.Quotient G B₁),
        (Smap G adjA B₁).submatrix e₁.symm e₀.symm = blockDiagonal fun _ => adjMatrix adjA) ∧
    (∃ (e₀ : BPVert G A₀ B₀ ≃ B₀ × orbitRel.Quotient G A₀)
        (e₁ : BPVert G A₀ B₁ ≃ B₁ × orbitRel.Quotient G A₀),
        (Tmap G adjB A₀).submatrix e₁.symm e₀.symm = blockDiagonal fun _ => adjMatrix adjB) ∧
    (∃ (e₀ : BPVert G A₁ B₀ ≃ B₀ × orbitRel.Quotient G A₁)
        (e₁ : BPVert G A₁ B₁ ≃ B₁ × orbitRel.Quotient G A₁),
        (Tmap G adjB A₁).submatrix e₁.symm e₀.symm = blockDiagonal fun _ => adjMatrix adjB) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
