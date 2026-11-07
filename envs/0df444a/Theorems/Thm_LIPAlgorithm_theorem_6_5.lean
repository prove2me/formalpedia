-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_6_5
-- name    : LIPAlgorithm.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:16.307906+00:00
-- url     : https://prove2.me/theorems/63399203-b452-4658-b080-6ab4563558d2
-- title:
--   Theorem 6.5 — exact marker label
-- statement:
--   Let $L_1,L_2$ be integral well-rounded lattices of rank $n\ge1$ and $w_i\in L_i^*$.
--
--   1. If there is $O\in\mathrm{Iso}(L_1,L_2)$ with $Ow_1=w_2$, the labels of $(L_1,w_1)$ and $(L_2,w_2)$ are equal.
--   2. If the labels are equal, then
--   $$S(w_1,w_2)=\{O\in\mathrm{Iso}(L_1,L_2):Ow_1=w_2\}=\{O_U\oplus O_R\}$$
--   over the residual witnesses $O_R$, and this set is nonempty. Hence the labels are equal if and only if $S(w_1,w_2)\ne\emptyset$.
--   3. There is a deterministic machine that, given Gram matrices of bases of $L_1,L_2$ and the pairings of resolving markers $w_1,w_2$ with these bases, with equal labels, outputs a duplicate-free list of exactly the coordinate matrices of the maps in $S(w_1,w_2)$, within $2^{Cn}(\ell+1)^K$ steps.
--
--   This is what turns a birthday collision into isomorphisms.
--
--   Differences from the source:
--   - reading: the lifting routine Lift, in an unnamed machine model → one Mathlib TM2 machine, with runs counted per input (Turing.TM2OutputsInTime); reason: the paper names no model; TM2 is the strongest standard reading, and every step of Lift costs 2^{O(n)} times a polynomial, a class closed under the polynomial overhead of simulating it on stacks, so the bound survives
--   - encoding: Lab(L₁, w₁) = Lab(L₂, w₂), the equality of canonical strings → LabelEq, the predicate that Theorem 5.14 and the Target primitive state to be equal to it; reason: the printed proof uses only these properties; Can is existential in theorem_5_14
--   - generalization: wᵢ resolving, in (a), in (b)'s set equality and in the iff → every wᵢ ∈ Lᵢ*; the resolving hypothesis is kept for the time clause; reason: resolving bounds only the cost; resolving markers are a subclass
--   - encoding: Lift(L₁, L₂, w₁, w₂) in 2^{O(n)} time → a machine on (G₁, G₂, pairings of w₁, w₂ with the bases), within 2^{Cn}·(ℓ+1)^K steps, with output matrices U, O b₁,ᵢ = ∑ₖ U_{k,i} b₂,ₖ; reason: inputs are Gram matrices throughout (§2.2), Remark 2.2 gives the factor, and U is the source-to-target matrix of Algorithm 1
--   - reading: 'L₁, L₂ well-rounded lattices' → integral well-rounded lattices; reason: §6 applies Lemma 6.1 to full-rank integral lattices, and p.9 says 'We work with integral lattices'
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 6.5, p.32; §6.1, p.31

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_RunsWithin
import Definitions.Def_LIPAlgorithm_LabelEq

open ExponomialAssortment.FPTAS

namespace LIPAlgorithm

/-- **Theorem 6.5 (Exact marker label).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 6.5,
p.32 (PDF p.35).

First part: (a) `O ∈ Iso(L₁, L₂)` with `Ow₁ = w₂` gives equal labels. (b) Equal labels give
`S(w₁, w₂) = {O_U ⊕ O_R}`, over the residual witnesses `O_R`, and `S(w₁, w₂) ≠ ∅`; hence equal labels occur if and only if
`S(w₁, w₂)` is nonempty. These hold for every `wᵢ ∈ Lᵢ*`.

Second part, the running time in (b): a deterministic machine `Lift`, given the Gram matrices `Gᵢ` of bases `bᵢ` and the
integer coordinates `yᵢ = (⟨wᵢ, bᵢ,ₖ⟩)ₖ` of resolving markers with equal labels, outputs in `2^{O(n)}` time, up to the polynomial of
Remark 2.2, a duplicate-free list of exactly the matrices `U` of the maps in `S(w₁, w₂)`.

**Formalization Note.** `Lab` is the predicate `LabelEq`. The hypothesis "resolving" bounds only the cost, so it is required only in the
second part. `O_U ⊕ O_R` is the isometry `O` with `O u_{1,j} = u_{2,j}` on `J(w₁)` and `O = O_R` on `U(w₁)⊥`. A marker is written through its
pairings with the basis, which determine it. The matrix `U` of `O` is the source-to-target matrix `O b₁,ᵢ = ∑ₖ U_{k,i} b₂,ₖ` of Algorithm 1,
p.39, so that `G₁ = U⊤G₂U`. -/
theorem theorem_6_5 :
    (∀ (n : ℕ) (L₁ L₂ : Submodule ℤ (E n)) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
        [DiscreteTopology L₂] [IsZLattice ℝ L₂] (w₁ w₂ : E n), 1 ≤ n →
      IsIntegralLattice L₁ → IsIntegralLattice L₂ → IsWellRounded L₁ → IsWellRounded L₂ →
      w₁ ∈ RegevLWE.GaussConv.dual L₁ → w₂ ∈ RegevLWE.GaussConv.dual L₂ →
        (∀ O ∈ isoLat L₁ L₂, O w₁ = w₂ → LabelEq L₁ w₁ L₂ w₂) ∧
        (LabelEq L₁ w₁ L₂ w₂ →
          (∀ O : E n ≃ₗᵢ[ℝ] E n, (O ∈ isoLat L₁ L₂ ∧ O w₁ = w₂) ↔
            ∃ OR ∈ residualWitness L₁ w₁ L₂ w₂,
              (∀ j ∈ fixedSteps L₁ w₁, O (fixedVec L₁ j w₁) = fixedVec L₂ j w₂) ∧
              ∀ y : ↥(fixedSpan L₁ w₁)ᗮ, O y = ((OR y : ↥(fixedSpan L₂ w₂)ᗮ) : E n)) ∧
          ∃ O ∈ isoLat L₁ L₂, O w₁ = w₂) ∧
        (LabelEq L₁ w₁ L₂ w₂ ↔ ∃ O ∈ isoLat L₁ L₂, O w₁ = w₂)) ∧
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ),
      ∀ (n : ℕ) (b₁ b₂ : Fin n → E n) (G₁ G₂ : Gram n) (y₁ y₂ : Fin n → ℤ) (w₁ w₂ : E n), 1 ≤ n →
        LinearIndependent ℝ b₁ → LinearIndependent ℝ b₂ →
        (∀ i k, inner ℝ (b₁ i) (b₁ k) = (G₁ i k : ℝ)) → (∀ i k, inner ℝ (b₂ i) (b₂ k) = (G₂ i k : ℝ)) →
        (∀ k, inner ℝ w₁ (b₁ k) = (y₁ k : ℝ)) → (∀ k, inner ℝ w₂ (b₂ k) = (y₂ k : ℝ)) →
        IsWellRounded (Submodule.span ℤ (Set.range b₁)) → IsWellRounded (Submodule.span ℤ (Set.range b₂)) →
        IsResolving (Submodule.span ℤ (Set.range b₁)) w₁ → IsResolving (Submodule.span ℤ (Set.range b₂)) w₂ →
        LabelEq (Submodule.span ℤ (Set.range b₁)) w₁ (Submodule.span ℤ (Set.range b₂)) w₂ →
        let inp := encInst G₁ G₂ ++ (List.finRange n).flatMap (fun k => encodeInt (y₁ k)) ++
          (List.finRange n).flatMap (fun k => encodeInt (y₂ k))
        ∃ Us : List (Gram n), Us.Nodup ∧
          (∀ U, U ∈ Us ↔ ∃ O ∈ isoLat (Submodule.span ℤ (Set.range b₁)) (Submodule.span ℤ (Set.range b₂)),
            O w₁ = w₂ ∧ ∀ i, O (b₁ i) = ∑ k, (U k i : ℝ) • b₂ k) ∧
          RunsWithin M inp (encMatList Us) (2 ^ (C * n) * (inp.length + 1) ^ K) := by sorry

end LIPAlgorithm
