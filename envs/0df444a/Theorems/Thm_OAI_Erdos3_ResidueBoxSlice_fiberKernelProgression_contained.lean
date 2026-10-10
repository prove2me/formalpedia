-- Prove2me | Theorems.Thm_OAI_Erdos3_ResidueBoxSlice_fiberKernelProgression_contained
-- name    : OAI.Erdos3.ResidueBoxSlice.fiberKernelProgression_contained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T01:06:27.692984+00:00
-- url     : https://prove2.me/theorems/86bb14d7-0f54-4f6d-8167-3a8f7d5806f7
-- title:
--   Each kernel coordinate progression of a residue box slice lies in its interval
-- statement:
--   Let $G$, $D$ be finite types with decidable equality, $B_d$ ($d \in D$) finite types with decidable equality, $h : D \to \mathbb{N}$, and write `PrincipalTupleIndex B h` $= \Sigma_d\, B_d \times \mathrm{Fin}(h_d)$. Let $L_G : G \to \mathbb{N}$ and $L : $ `PrincipalTupleIndex B h` $\to \mathbb{N}$, let $\mathrm{keep}$ be a decidable predicate on $G \oplus$ `PrincipalTupleIndex B h`, let $q \in \mathbb{N}$, and let $S$ be a `ResidueBoxSlice` of step $q$ for the side lengths $k \mapsto (L_G \sqcup L)(k)$ on the kept indices $k$ (OpenAI's structure of start points $S.\mathrm{start}_k \in \mathbb{N}$ and lengths $S.\mathrm{length}_k \in \mathbb{N}$ with $S.\mathrm{start}_k + qj < (L_G \sqcup L)(k)$ for all $j < S.\mathrm{length}_k$). Assume every index $\mathrm{inl}(g)$, $g \in G$, is kept (these are the section variables the statement uses). Then for every $g \in G$, the set `integerProgressionSupport (S.start (inl g)) q (S.length (inl g))`, that is $\{S.\mathrm{start}_{\mathrm{inl}\,g} + q n : n \in \mathbb{Z},\ 0 \le n < S.\mathrm{length}_{\mathrm{inl}\,g}\}$, is contained in the integer interval $[0, L_G(g))$.
--
--   Lean: `OAI.Erdos3.ResidueBoxSlice.fiberKernelProgression_contained` in `lean/OAI/Combinatorics/Progressions/Linear/KernelPrincipalFiberSliceLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B147` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/KernelPrincipalFiberSliceLaw.lean#L40

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B147

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

namespace ResidueBoxSlice

variable {B h LG L}
variable {keep : G ⊕ PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun k : {k // keep k} => Sum.elim LG L k.val) q)
variable (hlen : ∀ k, 0 < S.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < ((Sum.elim LG L k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

omit [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] [DecidablePred keep] in
theorem fiberKernelProgression_contained (g : G) :
    integerProgressionSupport (S.start ⟨Sum.inl g, hkernel g⟩ : ℤ) (q : ℤ)
        (S.length ⟨Sum.inl g, hkernel g⟩) ⊆ Finset.Ico (0 : ℤ) (LG g : ℤ) := by
  sorry

end ResidueBoxSlice
end Erdos3
end
end OAI
