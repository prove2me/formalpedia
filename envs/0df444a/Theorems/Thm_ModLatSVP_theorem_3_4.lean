-- Prove2me | Theorems.Thm_ModLatSVP_theorem_3_4
-- name    : ModLatSVP.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:58.771195+00:00
-- url     : https://prove2.me/theorems/5e605f76-fb67-41f3-87ab-fd52fde882b4
-- title:
--   Theorem 3.4 — exact module-SVP in $2^{O(N)}\mathrm{poly}(B,N)$ time and polynomial space, chain supplied
-- statement:
--   Fix integers $n_0,d_0\ge1$, $s_0\ge2$ and a rational $C_0\ge1$. There are a deterministic Turing machine and constants $C,k,k'$, depending only on $n_0,d_0,s_0,C_0$, with the following property. Let $K=K_0$ be a totally real or CM field with $\mathrm{rd}(K)\le C_0$, and suppose the input supplies a chain
--
--   $$K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h,\qquad [K_j:K_{j+1}]\le s_0,\qquad [K_h:\mathbb Q]\le d_0,$$
--
--   with integral bases, multiplication tables, inclusions and involutions. For every nonzero $\mathcal O_K$-module $M$ of rank at most $n_0$ in the input model of §2.2, with $N=\mathrm{rank}_{\mathbb Z}M$ and input length $\ell$ (module data and chain data), the machine outputs a shortest nonzero vector of $M$ within
--
--   $$2^{C N}\,(\ell+1)^{k}\ \text{steps},$$
--
--   using working space at most $(\ell+1)^{k'}$.
--
--   This is the SVP half of the paper's first main result in the setting where the subfield chain is given; Corollary 3.7 removes that assumption.
--
--   Differences from the source:
--   - reading: deterministic algorithm, bit complexity, no machine model named → one deterministic Mathlib TM2 machine over Bool, run per input; halts within the budget with exactly the stated output (SpikyCVP.RunsWithin); reason: the bounds are up to polynomial factors in the input length, and 2^{O(N)}·poly(ℓ) time with poly(ℓ) space is closed under the polynomial overhead of simulating a word-RAM
--   - reading: polynomial working space; a write-only output stream is excluded from working space (§2.1, p.11) → SpaceWithin M inp ((ℓ+1)^{k'}): on every reachable configuration the stacks other than the output stack hold at most (ℓ+1)^{k'} symbols, and the output stack is append-only; reason: Mathlib has no space measure for TM2; counting the input stack costs nothing since the budget exceeds ℓ
--   - reading: poly(B, N) with B the bit length of the input (chain data included) → (ℓ+1)^k with ℓ the length of the encoded input; the constants C, k, k' are chosen after n₀, d₀, s₀, C₀ and before the instance; reason: B ≤ ℓ and N ≤ ℓ, so poly(B, N) and poly(ℓ) are the same class; 'the implied constants depend only on n₀, s₀, d₀, C₀'
--   - encoding: a module over 𝒪_{K₀} in the input model of §2.2 (field data and action matrices in the input) → ∀ number fields K : Type with involution τ and data (ω, c, S, G, A) satisfying RepresentsField and RepresentsModule; the machine reads only the encoded data; reason: the machine sees only the data, so ∀ K with representation predicates is the promise that the data represent some K; every number field is isomorphic to one in Type
--   - encoding: rd(K₀) ≤ C₀; nonzero module of rank at most n₀ → |∆_K| ≤ C₀^{[K:ℚ]}; 1 ≤ N ≤ n₀ [K:ℚ] (ModulePromise); reason: rd(K) = |∆_K|^{1/[K:ℚ]}; the module rank is N/[K:ℚ]
--   - encoding: a supplied chain of totally real or CM fields with integral bases, multiplication tables, inclusions, and involutions ⋆ compatible with the inclusions → a list of FieldLevel records (degree, table, involution matrix, inclusion matrix into K's integral basis) satisfying RepresentsChain; the chain fields being totally real or CM is not assumed; reason: inclusions into K determine the inclusions between levels by linear algebra; every subfield of a totally real or CM field is totally real or CM (ModLatSVP.subfield_star)
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 3.4, §3.3, p.20 (PDF p.20)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_TowerPromise
import Definitions.Def_ModLatSVP_RepresentsChain
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField

namespace ModLatSVP

/-- **Theorem 3.4, §3.3, p.20: exact module-SVP with a supplied subfield chain.** Kim, Lee, Son, *Exact SVP
and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission
(manuscript sha256 e7151fad…): "Fix integers n₀, d₀ ≥ 1, s₀ ≥ 2, and a rational constant C₀ ≥ 1. Suppose
the input supplies a chain of totally real or CM fields K₀ ⊋ ⋯ ⊋ K_h, [K_j : K_{j+1}] ≤ s₀,
[K_h : ℚ] ≤ d₀, rd(K₀) ≤ C₀, together with integral bases, multiplication tables, inclusions, and
involutions ⋆ compatible with the inclusions. For any nonzero 𝒪_{K₀}-module M of rank at most n₀ in the
input model of Section 2.2, exact SVP can be solved deterministically in time 2^{O(N)} poly(B, N) and
polynomial space, where N = rank_ℤ M and B includes the chain data. The implied constants depend only on
n₀, s₀, d₀, C₀."

There are a TM2 machine and constants `C, k, k'` (depending only on `n₀, d₀, s₀, C₀`) such that for every
totally real or CM field `K` with `rd(K) ≤ C₀`, every module input `(d, c, S, G, A)` of `ℤ^N`
(`1 ≤ N ≤ n₀ [K:ℚ]`) and every supplied chain `Ls`, on the input `ℓ` bits long the machine outputs a
shortest nonzero vector of the module within `2^{C·N} (ℓ+1)^k` steps, using working space at most
`(ℓ+1)^{k'}`.

**Formalization Note.** The machine is Mathlib's TM2 (`SpikyCVP.RunsWithin`: halts within the budget
with the given output), deterministic; the paper names no machine, and `2^{O(N)} poly(ℓ)` time with
`poly(ℓ)` space is closed under the polynomial overhead of simulating a word-RAM. `ℓ` is the length of
the whole input (module data and chain data); `B ≤ ℓ` and `N ≤ ℓ`, so `poly(B, N)` is `poly(ℓ)`.
Working space is `SpaceWithin` (output stack excluded, append-only). The chain's fields being totally
real or CM is not assumed: it follows from `K` being so (`ModLatSVP.subfield_star`). -/
theorem theorem_3_4 (n₀ d₀ s₀ : ℕ) (hn₀ : 1 ≤ n₀) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) (C₀ : ℚ)
    (hC₀ : 1 ≤ C₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k k' : ℕ),
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ)
        (Ls : List (FieldLevel d)),
        IsStar K τ → RepresentsField K τ ω c S → RepresentsModule K τ ω G A →
        ModulePromise K n₀ C₀ N → RepresentsChain K τ ω s₀ d₀ Ls →
        (∃ x : Fin N → ℤ, IsShortest G x ∧
          SpikyCVP.RunsWithin M (encModule d N c S G A ++ encChain Ls) (encIntVec x)
            (2 ^ (C * N) * ((encModule d N c S G A ++ encChain Ls).length + 1) ^ k)) ∧
        SpaceWithin M (encModule d N c S G A ++ encChain Ls)
          (((encModule d N c S G A ++ encChain Ls).length + 1) ^ k') := by sorry

end ModLatSVP
