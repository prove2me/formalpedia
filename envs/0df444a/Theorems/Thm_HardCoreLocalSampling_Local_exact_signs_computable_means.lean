-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_exact_signs_computable_means
-- name    : HardCoreLocalSampling.Local.exact_signs_computable_means
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:43.485856+00:00
-- url     : https://prove2.me/theorems/32f95606-ac5f-43d8-baa1-dacea9129e84
-- title:
--   Lemma 17 — Exact signs of computable means
-- statement:
--   Suppose $a\in[-1,1]$ admits certified precision-$L$ approximations in time polynomial in $K+L$, where the integer $K$ is known. One can generate a sign with mean $a$ exactly, in expected time polynomial in $K+1$.
--
--   Concretely, $a$ is a family $a(K,x)$ indexed by a known $K$ and a parameter list $x$ whose entries each have bit size at most $K$. The given program $A$, on input $(K,L,x)$, writes a dyadic within $2^{-L}$ of $a(K,x)$ within $p(K+L)$ work. The constructed sign program, on input $(K,x)$, halts almost surely, outputs $+1$ with probability exactly $(1+a(K,x))/2$, and has expected work at most $q(K+1)$. Endpoints $a=\pm1$ and exactly dyadic means are included; no exact-real test occurs.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - generalization: a single mean a with known K → a family a(K,x) with every entry of x of bit size at most K, with one program and polynomial for the family; reason: a single mean is recovered by a singleton family with empty parameter list; the coefficient application also permits uniform families
--   - generalization: the sign is generated from the approximation procedure → the approximation program may use any oracle and any randomness, provided its guarantee holds on every tape; reason: a program with no oracle and no randomness is the source's case
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 17, printed p.14 (PDF p.15)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Specs

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 17, printed p.14 (PDF p.15).
Given a program `A` that on input `(K, L, x)` writes a dyadic within `2^{-L}` of the mean
`a K x ∈ [-1,1]` (endpoints and dyadic values allowed) in time `p(K+L)`, with `x` of size at most `K`,
there is a program that on input `(K, x)` outputs a sign of mean `a K x` exactly (`true` is `+1`)
in expected time polynomial in `K + 1`, halting almost surely. Here `A` is given as code and the
sign program is constructed, uniformly over the valid inputs. -/
theorem exact_signs_computable_means (O : Oracle) (A : Program) (p : Polynomial ℕ)
    (Valid : ℕ → List ℕ → Prop) (a : ℕ → List ℕ → ℝ)
    (hsize : ∀ K x, Valid K x → ∀ e ∈ x, Nat.size e ≤ K)
    (ha : ∀ K x, Valid K x → |a K x| ≤ 1)
    (happrox : ∀ K x, Valid K x → ∀ (L : ℕ) (ω : ℕ → Bool) (ξ : ℕ → ℕ → Bool),
      ∃ c, finalConfig A O ω ξ { N := regsOf (K :: L :: x) } = some c ∧
        c.word ≤ p.eval (K + L) ∧ |readDyadic c 0 - a K x| ≤ (1 / 2 : ℝ) ^ L) :
    ∃ (P : Program) (q : Polynomial ℕ),
      ∀ K x, Valid K x →
        let init : Config := { N := regsOf (K :: x) }
        (∀ᵐ ω ∂fairMeasure, outcome P O ω noExt init ≠ none) ∧
        fairMeasure {ω | outcome P O ω noExt init = some true} =
          ENNReal.ofReal ((1 + a K x) / 2) ∧
        ∫⁻ ω, wordWork P O ω noExt init ∂fairMeasure ≤ (q.eval (K + 1) : ℕ) := by sorry

end HardCoreLocalSampling.Local
