-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_D_1
-- name    : ModLatSVP.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:26:49.921772+00:00
-- url     : https://prove2.me/theorems/781a9022-8bcd-4426-90d7-9b45b176b9d7
-- title:
--   Theorem D.1, p.55 — explicit dependence on $C_0\ge\mathrm{rd}(K_0)$ — SVP in time $C_0^{\frac{n+1}{2n}N}2^{O(N)}\mathrm{poly}$, CVP (all closest vectors) in $C_0^{(1+\frac1n)N}2^{O(N)}\mathrm{poly}$
-- statement:
--   Fix integers $n_0,d_0\ge1$ and $s_0\ge2$. Under the hypotheses of Theorem 3.4 — a totally real or CM field $K_0$, a supplied chain $K_0\supsetneq\cdots\supsetneq K_h$ with $[K_j:K_{j+1}]\le s_0$ and $[K_h:\mathbb Q]\le d_0$, and a nonzero $\mathcal O_{K_0}$-module $M$ of rank $n\le n_0$ and dimension $N$ in the input model of §2.2 — let $C_0\ge\max\{1,\mathrm{rd}(K_0)\}$ be any real number. Then:
--
--   1. exact SVP can be solved in time $\displaystyle C_0^{\frac{n+1}{2n}N}\,2^{CN}\,(\ell+1)^{k}$;
--   2. for every rational target $t$, exact CVP (one closest vector) and the enumeration of all closest vectors (each once) can be solved in time $\displaystyle C_0^{\left(1+\frac1n\right)N}\,2^{CN}\,(\ell+1)^{k}$;
--
--   where $\ell$ is the input length (module, chain data, and target) and the algorithms and the constants $C,k$ depend only on $n_0,s_0,d_0$, not on $C_0$.
--
--   This makes the dependence of Theorems 3.4 and 3.5 on the root-discriminant bound explicit.
--
--   **Formalization Note** TM2 machines with the base mission's time convention, chosen before $C_0$; no space clause, as in the source. $\mathrm{rd}(K_0)\le C_0$ is written $|\Delta_{K_0}|\le C_0^{[K_0:\mathbb Q]}$.
--
--   Differences from the source:
--   - generalization: algorithms for each C_0 (the statement fixes only the implied constants and polynomial factors independently of C_0) → one triple of machines M_SVP, M_CVP, M_all, chosen before C_0, serves every real C_0 ≥ 1; reason: the proof (p.55) says "The algorithms do not use C_0"; one machine for all C_0 gives the source's statement for each C_0
--   - reading: "can be solved in time …", constants and polynomial factors depending only on n_0, s_0, d_0 → TM2 machines M_SVP, M_CVP, M_all and C, k chosen after n_0, s_0, d_0 and before C_0 and the instance; steps ⌊C_0^{…} 2^{C·N} (ℓ + 1)^k⌋; reason: same model as the published Theorem 3.4; B, N, ℓ(t) ≤ ℓ
--   - encoding: exact CVP, including enumeration of all closest vectors → one machine outputting a closest vector, one outputting a duplicate-free list of exactly the closest vectors; reason: both tasks of the statement
--   - encoding: hypotheses of Theorem 3.4 with real C_0 ≥ max{1, rd(K_0)}; M of rank n ≤ n_0 and dimension N → IsStar, RepresentsField, RepresentsModule, RepresentsChain, K totally real or CM, real C_0 ≥ 1 with |Δ_K| ≤ C_0^{[K:ℚ]}, N = n·d with 1 ≤ n ≤ n_0; reason: the published Theorem 3.4's hypotheses; rd(K_0) ≤ C_0 without real roots; "nonzero" is n ≥ 1
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem D.1, p.55 (PDF p.55); hypotheses of Theorem 3.4, p.20

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_RepresentsChain
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest

open NumberField

namespace ModLatSVP

namespace Supplement

/-- **Theorem D.1, App. D, p.55: explicit root-discriminant dependence.** Kim, Lee, Son, *Exact SVP and CVP
in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "Assume the hypotheses of Theorem 3.4, except that C₀ ≥ max{1, rd(K₀)} may be any real number.
Let M have rank n ≤ n₀ over 𝒪_{K₀} and dimension N. Exact SVP can be solved in time
C₀^{((n+1)/(2n))N} 2^{O(N)} poly(B, N), and exact CVP, including enumeration of all closest vectors, in time
C₀^{(1+1/n)N} 2^{O(N)} poly(B, N, ℓ(t)). The implied constants and polynomial factors depend only on
n₀, s₀, d₀."

Fix `n₀, d₀ ≥ 1` and `s₀ ≥ 2`. There are TM2 machines `M_SVP`, `M_CVP`, `M_all` and constants `C, k`
(depending only on `n₀, s₀, d₀`, not on `C₀`) such that for every real `C₀ ≥ 1`, every totally real or CM
field `K = K₀` of degree `d` with `rd(K) ≤ C₀`, every module input `(d, c, S, G, A)` of a module `ℤ^N` of
rank `n`, `1 ≤ n ≤ n₀`, `N = n d`, and every supplied chain `Ls` (relative degrees `≤ s₀`, last degree
`≤ d₀`), with `ℓ` the input length:
1. `M_SVP` outputs a shortest nonzero vector within `C₀^{((n+1)/(2n)) N} 2^{C N} (ℓ + 1)^k` steps;
2. for every rational target `t`, `M_CVP` outputs one closest vector and `M_all` the list of all closest
   vectors (each once), each within `C₀^{(1 + 1/n) N} 2^{C N} (ℓ + 1)^k` steps.

**Formalization Note.**
* Hypotheses of `ModLatSVP.theorem_3_4` (field, module input, supplied chain `RepresentsChain`), with
  `rd(K₀) ≤ C₀` written `|∆_K| ≤ C₀^{[K:ℚ]}` for a real `C₀ ≥ 1`; "nonzero module of rank `n ≤ n₀`" is
  `N = n d` with `1 ≤ n ≤ n₀`.
* The machines and `C, k` are chosen before `C₀` ("depend only on `n₀, s₀, d₀`").
* The theorem bounds time only; no space clause is stated, as in the source. "Exact CVP, including
  enumeration of all closest vectors" is stated as both tasks. Machine and time as in
  `ModLatSVP.theorem_3_4`; `ℓ` includes the chain data and the target. -/
theorem theorem_D_1 (n₀ d₀ s₀ : ℕ) (hn₀ : 1 ≤ n₀) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) :
    ∃ (Msvp Mcvp Mall : Turing.TM2ComputableAux Bool Bool) (C k : ℕ),
      ∀ (C₀ : ℝ), 1 ≤ C₀ →
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (n d N : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ)
        (Ls : List (FieldLevel d)),
        (IsTotallyReal K ∨ IsCMField K) → |(discr K : ℝ)| ≤ C₀ ^ Module.finrank ℚ K →
        IsStar K τ → RepresentsField K τ ω c S → RepresentsModule K τ ω G A →
        1 ≤ n → n ≤ n₀ → N = n * d → RepresentsChain K τ ω s₀ d₀ Ls →
        (∃ x : Fin N → ℤ, IsShortest G x ∧
          SpikyCVP.RunsWithin Msvp (encModule d N c S G A ++ encChain Ls) (encIntVec x)
            ⌊C₀ ^ (((n : ℝ) + 1) / (2 * n) * N) * 2 ^ (C * N) *
              (((encModule d N c S G A ++ encChain Ls).length : ℝ) + 1) ^ k⌋₊) ∧
        ∀ t : Fin N → ℚ,
          (∃ x : Fin N → ℤ, IsClosest G t x ∧
            SpikyCVP.RunsWithin Mcvp (encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t)
              (encIntVec x)
              ⌊C₀ ^ ((1 + 1 / (n : ℝ)) * N) * 2 ^ (C * N) *
                (((encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k⌋₊) ∧
          (∃ xs : List (Fin N → ℤ), xs.Nodup ∧ (∀ x, x ∈ xs ↔ IsClosest G t x) ∧
            SpikyCVP.RunsWithin Mall (encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t)
              (xs.flatMap encIntVec)
              ⌊C₀ ^ ((1 + 1 / (n : ℝ)) * N) * 2 ^ (C * N) *
                (((encModule d N c S G A ++ encChain Ls ++ SpikyCVP.encVec t).length : ℝ) + 1) ^ k⌋₊) := by sorry

end Supplement

end ModLatSVP
