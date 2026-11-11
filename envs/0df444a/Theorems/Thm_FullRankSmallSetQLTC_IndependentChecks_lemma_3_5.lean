-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_lemma_3_5
-- name    : FullRankSmallSetQLTC.IndependentChecks.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:07:26.298502+00:00
-- url     : https://prove2.me/theorems/1e74ab64-83a6-425d-b7e9-58086a17fa19
-- title:
--   Lemma 3.5 — the orbit matrix of the line product is Σ_x C_x
-- statement:
--   Keep the setting of §3.1: two decorated cubical complexes $Y_L,Y_R$ of dimension $h=2^k$ on the same finite group $G$, nonempty signature sets $S_L,S_R$, the incidence graphs $I_L,I_R$ with middle types the Hadamard code $H$, and a binary matrix $C_x\in\mathbb F_2^{S_R\times S_L}$ used at the middle vertices of type $x\in H$. Under the distinct-witness condition (3.2), the orbit matrix of the line product, indexed by signatures, is
--   $$[A_C]=\sum_{x\in H}C_x .$$
--   More precisely, the edges witnessed at middle vertices of type $x$ have orbit matrix $C_x$.
--
--   Differences from the source:
--   - encoding: vertex orbits G × {σ} indexed by signatures → the orbit of (1, σ); reason: the orbit of (1, σ) under left translation is G × {σ}
--   - encoding: [A_C], the adjacency map of the quotient of the line product (a multigraph) → the orbit matrix of the simple graph of pairs with at least one witness; reason: under (3.2) every edge has a unique witness, so the line product is simple and the two agree
--   - encoding: signature sets S_L, S_R → injective families of signatures indexed by nonempty finite types; reason: a finite set is the image of an injective enumeration
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), Lemma 3.5, p. 15 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Cubical

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction

open Classical in
/-- **Lemma 3.5** (p. 15). Let `Y_L = Cay(G; A^L_1, …, A^L_h)`, `Y_R = Cay(G; A^R_1, …, A^R_h)` be
decorated cubical complexes of the same dimension `h = 2^k` on the same finite group `G`, with
nonempty signature sets `S_L`, `S_R`, and use a binary matrix `C_x ∈ 𝔽₂^{S_R × S_L}` at the middle
vertices of type `x ∈ H`. Under the distinct-witness condition (3.2), the orbit matrix of the
resulting line product, indexed by signatures (the orbit `G × {σ}` is the orbit of `(1, σ)`), is
`[A_C] = Σ_{x ∈ H} C_x`; more precisely, the edges witnessed at middle vertices of type `x` have
orbit matrix `C_x`. -/
theorem lemma_3_5 {G : Type*} [Group G] [Fintype G] [DecidableEq G] {k : ℕ}
    {ιL ιR : Type*} [Fintype ιL] [Fintype ιR] [DecidableEq ιL] [DecidableEq ιR]
    [Nonempty ιL] [Nonempty ιR]
    (AL AR : Fin (2 ^ k) → Set G) (hAL : IsCubicalGenSet AL) (hAR : IsCubicalGenSet AR)
    (sL : ιL → Sig G (2 ^ k)) (sR : ιR → Sig G (2 ^ k))
    (hsL : Function.Injective sL) (hsR : Function.Injective sR)
    (hsigL : ∀ σ, IsSignature AL (sL σ)) (hsigR : ∀ τ, IsSignature AR (sR τ))
    (C : (Fin (2 ^ k) → ZMod 2) → Matrix ιR ιL (ZMod 2))
    (hdw : DistinctWitness (fun σ => normCube AL (sL σ)) (fun τ => normCube AR (sR τ))) :
    (∀ (σ : ιL) (τ : ιR),
      orbitMatrix G (lpAdj (fun σ => normCube AL (sL σ)) (fun τ => normCube AR (sR τ)) C)
          (Quotient.mk (orbitRel G (Cell G ιR)) ⟨1, τ⟩)
          (Quotient.mk (orbitRel G (Cell G ιL)) ⟨1, σ⟩) =
        ∑ x ∈ hadamard k, C x τ σ) ∧
    (∀ x ∈ hadamard k, ∀ (σ : ιL) (τ : ιR),
      orbitMatrix G (lpAdjAt (fun σ => normCube AL (sL σ)) (fun τ => normCube AR (sR τ)) C x)
          (Quotient.mk (orbitRel G (Cell G ιR)) ⟨1, τ⟩)
          (Quotient.mk (orbitRel G (Cell G ιL)) ⟨1, σ⟩) =
        C x τ σ) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
