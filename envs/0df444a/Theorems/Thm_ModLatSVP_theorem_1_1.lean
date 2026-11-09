-- Prove2me | Theorems.Thm_ModLatSVP_theorem_1_1
-- name    : ModLatSVP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:38.737691+00:00
-- url     : https://prove2.me/theorems/ab7d787a-8bc6-43c1-b965-215bc879540b
-- title:
--   Theorem 1.1 (= Corollary 3.7) — deterministic $2^{O(N)}$-time polynomial-space exact SVP and all-closest-vectors CVP on bounded-rank modules over field towers
-- statement:
--   Fix integers $n_0,d_0\ge1$, $s_0\ge2$ and a rational $C_0\ge1$. There are two deterministic Turing machines, $M_{\mathrm{SVP}}$ and $M_{\mathrm{CVP}}$, and constants $C,k,k'$, depending only on $n_0,d_0,s_0,C_0$, with the following property.
--
--   Let $K$ be a totally real or CM number field with $\mathrm{rd}(K)\le C_0$ that **admits** a subfield chain $K=K_0\supsetneq\cdots\supsetneq K_h$ with $[K_j:K_{j+1}]\le s_0$ and $[K_h:\mathbb Q]\le d_0$ (the chain is not part of the input). Let $M$ be a nonzero $\mathcal O_K$-module of rank at most $n_0$ and lattice dimension $N$, given in the input model of §2.2 (integral basis data of $K$, a positive definite rational Gram matrix compatible with the action, and the action matrices), with input length $\ell$. Then
--
--   1. on this input, $M_{\mathrm{SVP}}$ outputs a shortest nonzero vector of $M$;
--   2. for every rational target $t$, on the input followed by $t$ (length $\ell_t$), $M_{\mathrm{CVP}}$ outputs the list of all closest vectors of $M$ to $t$, each exactly once;
--
--   each within $2^{CN}(\ell+1)^k$ (respectively $2^{CN}(\ell_t+1)^k$) steps and working space $(\ell+1)^{k'}$ (respectively $(\ell_t+1)^{k'}$), the output being written to a write-only stream.
--
--   For general $N$-dimensional lattices, the fastest known polynomial-space algorithms for exact SVP and CVP take $N^{\Theta(N)}$ time, and the known $2^{O(N)}$-time algorithms use exponential space. The theorem shows that, for modules over fields with bounded root discriminant and a bounded subfield chain, single-exponential time and polynomial space are achieved together; such fields exist in every degree (layers of infinite class field towers).
--
--   Differences from the source:
--   - reading: Theorem 1.1 (Informal): bounded rank, bounded root discriminant, a subfield chain with bounded relative degrees and bounded terminal degree; 'All bounded parameters are fixed independently of N' → Corollary 3.7: ∀ n₀, d₀ ≥ 1, s₀ ≥ 2, rational C₀ ≥ 1, ∃ machines and constants, ∀ instances satisfying TowerPromise K n₀ d₀ s₀ C₀ N; reason: Corollary 3.7 is the paper's formal version ('it can be recovered from the field representation (Corollary 3.7)', p.3); quantifiers in the order of Theorems 3.4/3.5
--   - reading: deterministic algorithm, bit complexity, no machine model named → one deterministic Mathlib TM2 machine over Bool, run per input; halts within the budget with exactly the stated output (SpikyCVP.RunsWithin); reason: the bounds are up to polynomial factors in the input length, and 2^{O(N)}·poly(ℓ) time with poly(ℓ) space is closed under the polynomial overhead of simulating a word-RAM
--   - reading: polynomial working space; a write-only output stream is excluded from working space (§2.1, p.11) → SpaceWithin M inp ((ℓ+1)^{k'}): on every reachable configuration the stacks other than the output stack hold at most (ℓ+1)^{k'} symbols, and the output stack is append-only; reason: Mathlib has no space measure for TM2; counting the input stack costs nothing since the budget exceeds ℓ
--   - reading: 2^{O(N)} time … up to factors polynomial in the input length → 2^{C·N}·(ℓ+1)^k steps, ℓ the length of the encoded input (target included for CVP); reason: B, N and ℓ(t) are at most ℓ
--   - reading: The bounds include recovering the subfield chain, constructing reduced module flags, and enumerating all closest vectors → no chain in the input (only the promise ∃ chain); the stated budgets bound the whole run; the reduced flags are internal and not output; reason: the flags are a step of the algorithm, whose cost the time bound covers; chain recovery and the listing of all closest vectors are stated explicitly
--   - encoding: a nonzero N-dimensional module lattice of bounded rank over a totally real or CM field K, equipped with a compatible rational inner product (input model of §2.2) → ∀ number fields K : Type with involution τ and data (ω, c, S, G, A) satisfying RepresentsField and RepresentsModule; 1 ≤ N ≤ n₀[K:ℚ]; reason: the machine sees only the data; the module rank is N/[K:ℚ]; every number field is isomorphic to one in Type
--   - encoding: K has bounded root discriminant (rd(K) ≤ C₀) and admits a subfield chain → |∆_K| ≤ C₀^{[K:ℚ]} and ∃ h F, IsChain K s₀ d₀ F h with F : ℕ → IntermediateField ℚ K (TowerPromise); reason: rd(K) = |∆_K|^{1/[K:ℚ]}; the chain's fields being totally real or CM is implied (ModLatSVP.subfield_star)
--   - reading: exact CVP … including enumeration of all closest vectors → the output is the concatenated encoding of a duplicate-free list xs with x ∈ xs ↔ IsClosest G t x; reason: the paper's enumeration outputs every point exactly once (Lemma 3.2, p.18); the stronger reading
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 1.1, p.2 (PDF p.2), at the strength of Corollary 3.7, p.23 (PDF p.23), i.e. Theorems 3.4 and 3.5, p.20, with the chain only promised

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_TowerPromise
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField

namespace ModLatSVP

/-- **Theorem 1.1, p.2, at the strength of its formal version Corollary 3.7, p.23.** Kim, Lee, Son, *Exact
SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission
(manuscript sha256 e7151fad…). Theorem 1.1: "Let M be a nonzero N-dimensional module lattice of bounded
rank over a totally real or CM field K, equipped with a compatible rational inner product. Suppose that K
has bounded root discriminant and admits a subfield chain with bounded relative degrees ending at a field
of bounded degree. Then exact SVP and CVP for every rational target can be solved deterministically in
2^{O(N)} time and polynomial space, up to factors polynomial in the input length. The bounds include
recovering the subfield chain, constructing reduced module flags, and enumerating all closest vectors.
All bounded parameters are fixed independently of N." Corollary 3.7: "The conclusions of Theorems 3.4
and 3.5 remain valid when the supplied subfield chain is replaced by the promise that such a chain
exists."

Fix `n₀, d₀ ≥ 1`, `s₀ ≥ 2` and a rational `C₀ ≥ 1`. There are TM2 machines `M_SVP`, `M_CVP` and constants
`C, k, k'` such that for every totally real or CM field `K` with `rd(K) ≤ C₀` that has a subfield chain
with relative degrees `≤ s₀` ending in degree `≤ d₀`, and every module input `(d, c, S, G, A)` of a
nonzero module `ℤ^N` of rank at most `n₀` (`ℓ` bits; no chain supplied):
1. `M_SVP` outputs a shortest nonzero vector within `2^{C·N}(ℓ+1)^k` steps and working space `(ℓ+1)^{k'}`;
2. for every rational target `t`, `M_CVP` on the input followed by `t` outputs the list of all closest
   vectors to `t`, each exactly once, within the same budgets (with `ℓ` the length of the longer input).

**Formalization Note.** The machine is Mathlib's TM2, deterministic, with time `SpikyCVP.RunsWithin` and
working space `SpaceWithin` (all stacks but the output stack, on every reachable configuration, output
append-only). `ℓ` is the length of the whole input; the field data are the multiplication table and the
involution matrix of an integral basis, which the module input includes (proof of Corollary 3.7). The
field `K` is quantified universally with representation predicates as hypotheses, and the chain only
through `TowerPromise`. `C, k, k'` and the machines are chosen after `n₀, d₀, s₀, C₀` and before the
instance. -/
theorem theorem_1_1 (n₀ d₀ s₀ : ℕ) (hn₀ : 1 ≤ n₀) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) (C₀ : ℚ)
    (hC₀ : 1 ≤ C₀) :
    ∃ (Msvp Mcvp : Turing.TM2ComputableAux Bool Bool) (C k k' : ℕ),
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ),
        IsStar K τ → RepresentsField K τ ω c S → RepresentsModule K τ ω G A →
        TowerPromise K n₀ d₀ s₀ C₀ N →
        ((∃ x : Fin N → ℤ, IsShortest G x ∧
            SpikyCVP.RunsWithin Msvp (encModule d N c S G A) (encIntVec x)
              (2 ^ (C * N) * ((encModule d N c S G A).length + 1) ^ k)) ∧
          SpaceWithin Msvp (encModule d N c S G A) (((encModule d N c S G A).length + 1) ^ k')) ∧
        ∀ t : Fin N → ℚ,
          (∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
            SpikyCVP.RunsWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t) (xs.flatMap encIntVec)
              (2 ^ (C * N) * ((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k)) ∧
          SpaceWithin Mcvp (encModule d N c S G A ++ SpikyCVP.encVec t)
            (((encModule d N c S G A ++ SpikyCVP.encVec t).length + 1) ^ k') := by sorry

end ModLatSVP
