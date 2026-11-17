-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_6_9
-- name    : ModLatSVP.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:26:22.96969+00:00
-- url     : https://prove2.me/theorems/0e6411a3-c840-4c09-a4a2-2c2674a6ddb1
-- title:
--   Theorem 6.9, p.44 — growing rank $n\ge2$ along a promised subfield chain — exact SVP in polynomial space and time $(N+6)^{n+2}2^{O(N)}n^{N/(2e)}\mathrm{poly}(B,N)$
-- statement:
--   Fix $s_0\ge2$, $d_0\ge1$ and $C_0\ge1$. Let $K$ be a totally real or CM field of degree $d$ with $\mathrm{rd}(K)\le C_0$ that admits a subfield chain $K=K_0\supsetneq\cdots\supsetneq K_h$ with $[K_j:K_{j+1}]\le s_0$ and $[K_h:\mathbb Q]\le d_0$ (the chain is not part of the input). Let $M\cong\mathbb Z^N$ be a rank-$n$ module over $\mathcal O_K$, $n\ge2$ part of the input, $N=nd$, in the input model of §2.2. Then a shortest nonzero vector of $M$ can be computed deterministically in polynomial working space and time
--
--   $$(N+6)^{n+2}\,2^{CN}\,n^{N/(2e)}\,(\ell+1)^{k},$$
--
--   $\ell$ the input length, where the machine and $C,k,k'$ depend only on $s_0,d_0,C_0$.
--
--   This extends the fixed-rank Theorem 3.4 to growing rank; for $n=(\log N)^{\gamma+o(1)}$, $0\le\gamma<1$, the time is $(\log N)^{\gamma N/(2e)+o(N)}\mathrm{poly}(B)$.
--
--   **Formalization Note** TM2 machine with the base mission's time and space conventions; the chain is only promised, as in the published goal. The rank is unbounded, so the base mission's $\texttt{ModulePromise}$ (rank $\le n_0$) is not used; $\mathrm{rd}(K)\le C_0$ is written $|\Delta_K|\le C_0^{d}$.
--
--   Differences from the source:
--   - generalization: C_0 (Theorem 3.4 takes a rational constant C_0 ≥ 1) → any real C_0 ≥ 1; reason: the statement for a real C_0 contains the rational case
--   - reading: "Fix s_0, d_0, and C_0" with a chain "as in Theorem 3.4" → s_0 ≥ 2, d_0 ≥ 1, C_0 ≥ 1; reason: the conventions of Theorem 3.4
--   - reading: "can be solved deterministically in polynomial space and time … poly(B, N)", constants depending only on s_0, d_0, C_0 → a TM2 machine and C, k, k' chosen after s_0, d_0, C_0 and before n and the instance; time ⌊(N + 6)^{n+2} 2^{C·N} n^{N/(2e)} (ℓ + 1)^k⌋, SpaceWithin (ℓ + 1)^{k'}; reason: same model as the published Theorem 3.4; B, N ≤ ℓ
--   - encoding: K admitting a subfield chain as in Theorem 3.4 (not supplied); rd(K) ≤ C_0 → ∃ h F, IsChain K s_0 d_0 F h; |Δ_K| ≤ C_0^{[K:ℚ]}; reason: the proof computes the chain when it is not supplied; same condition without real roots
--   - encoding: rank-n module over 𝒪_K → module input with RepresentsField, RepresentsModule, IsStar, N = n·d, 2 ≤ n; reason: the base mission's input model
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 6.9, p.44 (PDF p.44); hypotheses of Theorem 3.4, p.20

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_IsChain
import Definitions.Def_ModLatSVP_RepresentsModule
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin

open NumberField

namespace ModLatSVP

namespace Supplement

/-- **Theorem 6.9, §6.5, p.44: growing module rank via subfield descent.** Kim, Lee, Son, *Exact SVP and
CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…): "Fix s₀, d₀, and C₀. Let K be a totally real or CM field of degree d, with rd(K) ≤ C₀,
admitting a subfield chain as in Theorem 3.4. Let M be a rank-n module over 𝒪_K, where n ≥ 2 is part of
the input and N = nd. Exact SVP in M can be solved deterministically in polynomial space and time
(N + 6)^{n+2} 2^{O(N)} n^{N/(2e)} poly(B, N), where the implied constants depend only on s₀, d₀, C₀."

Fix `s₀ ≥ 2`, `d₀ ≥ 1` and a real `C₀ ≥ 1`. There are a TM2 machine `M` and constants `C, k, k'`
(depending only on `s₀, d₀, C₀`) such that for every totally real or CM field `K` of degree `d` with
`rd(K) ≤ C₀` that has a subfield chain `K = K₀ ⊋ ⋯ ⊋ K_h` with relative degrees `≤ s₀` and
`[K_h : ℚ] ≤ d₀`, every `n ≥ 2` and every module input `(d, c, S, G, A)` of a rank-`n` module `ℤ^N`
(`N = n d`, `ℓ` bits, no chain supplied), `M` outputs a shortest nonzero vector within
`(N + 6)^{n+2} 2^{C N} n^{N/(2e)} (ℓ + 1)^k` steps and working space `(ℓ + 1)^{k'}`.

**Formalization Note.**
* The chain is only promised (`∃ h F, IsChain K s₀ d₀ F h`), as in `ModLatSVP.theorem_1_1`; the paper's
  proof computes it when it is not supplied ("If the subfield chain is not supplied, compute it once").
* The rank is not bounded (`n ≥ 2` is part of the input), so `ModLatSVP.ModulePromise` (which bounds the
  rank by `n₀`) is not used; `rd(K) ≤ C₀` is `|∆_K| ≤ C₀^{[K:ℚ]}`.
* `C₀` is a real number (the theorem does not ask for a rational one); `s₀ ≥ 2`, `d₀ ≥ 1`, `C₀ ≥ 1` are
  the conventions of Theorem 3.4.
* Machine, time and space as in `ModLatSVP.theorem_3_4`; `poly(B, N)` is `(ℓ + 1)^k`. -/
theorem theorem_6_9 (d₀ s₀ : ℕ) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C k k' : ℕ),
      ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ),
        (IsTotallyReal K ∨ IsCMField K) → |(discr K : ℝ)| ≤ C₀ ^ Module.finrank ℚ K →
        (∃ (h : ℕ) (F : ℕ → IntermediateField ℚ K), IsChain K s₀ d₀ F h) →
        IsStar K τ → RepresentsField K τ ω c S → RepresentsModule K τ ω G A → N = n * d →
        (∃ x : Fin N → ℤ, IsShortest G x ∧
            SpikyCVP.RunsWithin M (encModule d N c S G A) (encIntVec x)
              ⌊((N : ℝ) + 6) ^ (n + 2) * 2 ^ (C * N) * (n : ℝ) ^ ((N : ℝ) / (2 * Real.exp 1)) *
                (((encModule d N c S G A).length : ℝ) + 1) ^ k⌋₊) ∧
        SpaceWithin M (encModule d N c S G A) (((encModule d N c S G A).length + 1) ^ k') := by sorry

end Supplement

end ModLatSVP
