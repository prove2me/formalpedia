-- Prove2me | Theorems.Thm_ModLatSVP_lemma_3_6_i
-- name    : ModLatSVP.lemma_3_6_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:24.799302+00:00
-- url     : https://prove2.me/theorems/5cc1711e-72f6-4a76-881f-3ce28dd6bc88
-- title:
--   Lemma 3.6(i) — finding a bounded subfield chain in $D^{O(\log D)}\mathrm{poly}(B,D)$ time and polynomial space
-- statement:
--   Fix integers $s_0\ge2$ and $d_0\ge1$. There are a deterministic Turing machine and constants $C,k,k',k''$ such that, for every totally real or CM field $K$ of degree $D$ given by an integral basis of $\mathcal O_K$, its multiplication table and its involution $\star$ (input length $\ell$), the machine runs within
--
--   $$(D+1)^{C\lceil\log_2(D+1)\rceil}\,(\ell+1)^{k}\ \text{steps}$$
--
--   and working space $(\ell+1)^{k'}$, and
--
--   1. if $K$ has no chain $K=K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h$ with $[K_j:K_{j+1}]\le s_0$ and $[K_h:\mathbb Q]\le d_0$, it reports that none exists;
--   2. otherwise it outputs such a chain, every field of which is totally real or CM with root discriminant at most $\mathrm{rd}(K)$, each given by an integral basis (expressed in that of $K$), its multiplication table and the matrix of the restriction of $\star$, the whole output having length at most $(\ell+1)^{k''}$.
--
--   This is how Corollary 3.7 recovers the chain from the field data alone; the $D^{O(\log D)}$ factor is absorbed into $2^{O(N)}$.
--
--   Differences from the source:
--   - encoding: Fix integers s₀, s₁ ≥ 2 and d₀ ≥ 1 → parameters s₀ ≥ 2 and d₀ ≥ 1 only; reason: s₁ is used only by clause (ii), which is a separate algorithm; this item is clause (i) with the lemma's closing sentence
--   - reading: deterministic algorithm, bit complexity, no machine model named → one deterministic Mathlib TM2 machine over Bool, run per input; halts within the budget with exactly the stated output (SpikyCVP.RunsWithin); reason: the bounds are up to polynomial factors in the input length, and 2^{O(N)}·poly(ℓ) time with poly(ℓ) space is closed under the polynomial overhead of simulating a word-RAM
--   - reading: polynomial working space; a write-only output stream is excluded from working space (§2.1, p.11) → SpaceWithin M inp ((ℓ+1)^{k'}): on every reachable configuration the stacks other than the output stack hold at most (ℓ+1)^{k'} symbols, and the output stack is append-only; reason: Mathlib has no space measure for TM2; counting the input stack costs nothing since the budget exceeds ℓ
--   - reading: time D^{O(log D)} poly(B, D) → (D+1)^{C·⌈log₂(D+1)⌉}·(ℓ+1)^k with D = d and ℓ the length of the encoded field data; C, k, k', k'' chosen after s₀, d₀ and before the instance; reason: the same class: D^{c log D} ≤ (D+1)^{c⌈log₂(D+1)⌉}·const and conversely; B = ℓ and D ≤ ℓ
--   - reading: reports that none exists; returns the chain … all of polynomial encoding length → outputs [false]; or outputs true followed by encChain Ls with RepresentsChainAt, and encChain Ls has length ≤ (ℓ+1)^{k''}; reason: a binary output must distinguish the two answers; the length bound is 'polynomial encoding length'
--   - encoding: K given by an integral basis of 𝒪_K, its multiplication table, and its involution ⋆ → ∀ number fields K : Type with τ and (ω, c, S) satisfying RepresentsField; the input is encField d c S; reason: the machine sees only the data
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Lemma 3.6(i) and the closing sentence of Lemma 3.6, §3.4, p.21 (PDF p.21)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsChain
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField

namespace ModLatSVP

/-- **Lemma 3.6(i), §3.4, p.21, with the lemma's closing sentence: recovering the subfield chain.** Kim,
Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…): "Fix integers s₀, s₁ ≥ 2 and d₀ ≥ 1. Let K be a totally real or
CM field of degree D, given by an integral basis of 𝒪_K, its multiplication table, and its involution ⋆,
with total input length B. Then the following algorithms exist. (i) A deterministic algorithm finds a
chain K = K₀ ⊋ K₁ ⊋ ⋯ ⊋ K_h with [K_j : K_{j+1}] ≤ s₀ and [K_h : ℚ] ≤ d₀, if one exists, and otherwise
reports that none exists. It runs in time D^{O(log D)} poly(B, D) and polynomial working space. […] Every
field produced is totally real or CM, has root discriminant at most rd(K), and is returned with an
integral basis, multiplication table, involution, and inclusion into K, all of polynomial encoding
length. The involution on each subfield is the restriction of ⋆."

There are a TM2 machine and constants `C, k, k', k''` (depending only on `s₀, d₀`) such that for every
totally real or CM field `K` of degree `D = d` given by its field data (`ℓ` bits), within
`(D+1)^{C ⌈log₂(D+1)⌉} (ℓ+1)^k` steps and working space `(ℓ+1)^{k'}`:
1. if no such chain exists, the machine outputs the failure code `[false]`;
2. if one exists, it outputs `true` followed by the data `Ls` of a chain `K = F 0 ⊋ ⋯ ⊋ F h` with the
   bounds, every `F j` totally real or CM with `rd(F j) ≤ rd(K)`, each level given by an integral basis
   (in coordinates of `K`), its multiplication table and the matrix of the restriction of `⋆`, the
   encoding of `Ls` being at most `(ℓ+1)^{k''}` bits long.

**Formalization Note.** Clause (ii) and the parameter `s₁`, which only (ii) uses, are not stated.
`D^{O(log D)} poly(B, D)` is the class `(D+1)^{C ⌈log₂(D+1)⌉} (ℓ+1)^k` with `C` fixed before the
instance; `B` is the input length `ℓ`, and `D ≤ ℓ`. Machine and working space as in
`ModLatSVP.theorem_3_4`. -/
theorem lemma_3_6_i (s₀ d₀ : ℕ) (hs₀ : 2 ≤ s₀) (hd₀ : 1 ≤ d₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k k' k'' : ℕ),
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ),
        (IsTotallyReal K ∨ IsCMField K) → IsStar K τ → RepresentsField K τ ω c S →
        SpaceWithin M (encField d c S) (((encField d c S).length + 1) ^ k') ∧
        ((¬ ∃ (h : ℕ) (F : ℕ → IntermediateField ℚ K), IsChain K s₀ d₀ F h) →
          SpikyCVP.RunsWithin M (encField d c S) [false]
            ((d + 1) ^ (C * Nat.clog 2 (d + 1)) * ((encField d c S).length + 1) ^ k)) ∧
        ((∃ (h : ℕ) (F : ℕ → IntermediateField ℚ K), IsChain K s₀ d₀ F h) →
          ∃ (Ls : List (FieldLevel d)) (F : ℕ → IntermediateField ℚ K),
            IsChain K s₀ d₀ F Ls.length ∧ RepresentsChainAt K τ ω F Ls ∧
            (∀ j ≤ Ls.length, (IsTotallyReal (F j) ∨ IsCMField (F j)) ∧ rd (F j) ≤ rd K) ∧
            (encChain Ls).length ≤ ((encField d c S).length + 1) ^ k'' ∧
            SpikyCVP.RunsWithin M (encField d c S) (true :: encChain Ls)
              ((d + 1) ^ (C * Nat.clog 2 (d + 1)) * ((encField d c S).length + 1) ^ k)) := by sorry

end ModLatSVP
