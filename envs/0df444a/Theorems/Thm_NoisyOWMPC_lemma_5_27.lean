-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_27
-- name    : NoisyOWMPC.lemma_5_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:59:14.735188+00:00
-- url     : https://prove2.me/theorems/4530f807-16b7-4b81-a47f-fabe122be8b2
-- title:
--   Lemma 5.27 — seed puncturing
-- statement:
--   Let $i\mathcal O$ be an indistinguishability obfuscator and $F$ an injective one-way function with input length $n(\lambda)$. Let a sampler state $\mathrm{st}$ be sampled by a PPT algorithm independently of a uniform seed $\sigma\in\{0,1\}^\kappa$ with $\kappa\ge n(\lambda)$, and let $P_{\mathrm{st},\sigma}$ and $P^0_{\mathrm{st}}$ be circuits computed in polynomial time from $(\mathrm{st},\sigma)$ and from $\mathrm{st}$, with common input and output lengths. Suppose a deterministic polynomial-time $\mathrm{Rec}(\mathrm{st},w)$ returns a list of seeds with
--   $$\Pr_{\mathrm{st},\sigma}\bigl[\forall w:\ P_{\mathrm{st},\sigma}(w)\ne P^0_{\mathrm{st}}(w)\implies\sigma\in\mathrm{Rec}(\mathrm{st},w)\bigr]\ge1-\delta .\qquad(5.15)$$
--   Then, with both circuits padded to a common polynomial size $s\ge s_0$, for every side information $z$ computed in polynomial time from $\mathrm{st}$,
--   $$(z,i\mathcal O(P_{\mathrm{st},\sigma}))\approx^c_\delta(z,i\mathcal O(P^0_{\mathrm{st}})).$$
--
--   This is the step the security proof applies to every recoverable object in turn.
--
--   Differences from the source:
--   - generalization: 'assuming iO and one-way functions', with n(λ) the input length of the paper's fixed injective OWF F → every iO scheme and every injective one-way function F (Definition 3.3), with κ ≥ F's input length; reason: the paper's F (from Theorem 3.4) is one such function
--   - generalization: circuits 'padded to the same size' → every polynomial pad size s above some polynomial s₀; reason: the paper's common public size is one such s
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - encoding: Definition 3.2: iO returns a circuit with 'polynomially bounded description'; obfuscations 'padded to a fixed public length' (p.21) → IOScheme carries a public length bound len(λ, n, s), polynomial and computable in polynomial time, on every obfuscated description; reason: every obfuscator with polynomially bounded descriptions has such a bound; it fixes the public transmission length
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.27, p.32

import Mathlib
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_NoisyOWMPC_CoinAlg
import Definitions.Def_NoisyOWMPC_construction

namespace NoisyOWMPC

open LaconicBarrier

/-- **Lemma 5.27 (Seed puncturing)** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), Lemma 5.27, p.32): "Let a sampler state `st` be sampled by a PPT algorithm independently
of a uniform seed `σ ∈ {0,1}^κ` with `κ ≥ n(λ)`, and let `P_{st,σ}` and `P⁰_st` be circuits computed
from `(st, σ)` and from `st`, respectively, with common input and output lengths. Suppose a
deterministic polynomial-time algorithm `Rec(st, w)` returns a polynomial-size list of seeds such
that `Pr_{st,σ}[∀w : P_{st,σ}(w) ≠ P⁰_st(w) ⟹ σ ∈ Rec(st, w)] ≥ 1 − δ` (5.15). Then, assuming iO
and one-way functions, for every side information `z` computed from `st`,
`(z, iO(P_{st,σ})) ≈^c_δ (z, iO(P⁰_st))`."

Here `n(λ)` is the input length of the injective one-way function `F` of the paper's conventions
(§5, p.21: "Write `F` for an injective one-way function family (Definition 3.3), which exists under
iO and one-way functions by Theorem 3.4").

**Formalization Note** "Assuming iO and one-way functions" is an iO scheme `O` and an injective
one-way function `F` (which they give by Theorem 3.4). The compared circuits are padded to a common
size `s` (proof, p.32: "pad all compared circuits to the same size"); the conclusion holds for every
polynomial `s` above some polynomial `s₀`. The sampler is a PPT coin algorithm run on `1^λ`; `P`,
`P⁰`, `Rec` and `z` are deterministic polynomial-time maps of their arguments. -/
theorem lemma_5_27 (O : IOScheme) (hO : O.IsIO) (Finj : KeyedFamily) (hF : Finj.IsInjOWF)
    (Samp : CoinAlg) (hSamp : Samp.IsPPT) (κ : ℕ → ℕ) (hκ : PolyBounded κ)
    (hκn : ∀ lam, Finj.n lam ≤ κ lam) (nin nout : ℕ → ℕ)
    (P : (lam : ℕ) → List Bool → (Fin (κ lam) → Bool) → MCircuit (nin lam))
    (P0 : (lam : ℕ) → List Bool → MCircuit (nin lam))
    (hP : PolyTimeOn (ι := (lam : ℕ) × List Bool × (Fin (κ lam) → Bool))
      (fun z => [unary z.1, z.2.1, bits z.2.2]) (fun z => (P z.1 z.2.1 z.2.2).code))
    (hP0 : PolyTimeOn (ι := (lam : ℕ) × List Bool) (fun z => [unary z.1, z.2])
      (fun z => (P0 z.1 z.2).code))
    (hout : ∀ lam st σ, (P lam st σ).outs.length = nout lam ∧ (P0 lam st).outs.length = nout lam)
    (Rec : (lam : ℕ) → List Bool → List Bool → List (Fin (κ lam) → Bool))
    (hRec : PolyTimeOn (ι := (lam : ℕ) × List Bool × List Bool)
      (fun z => [unary z.1, z.2.1, z.2.2])
      (fun z => QAdvFew.PoQOracle.tup ((Rec z.1 z.2.1 z.2.2).map bits)))
    (δ : ℕ → ℝ)
    (h515 : ∀ lam, 1 - δ lam ≤ wprob (unifW ((Fin (Samp.coins lam) → Bool) × (Fin (κ lam) → Bool)))
      (fun z => ∀ w : List Bool, w.length = nin lam →
        (P lam (Samp.run lam [] z.1) z.2).eval w ≠ (P0 lam (Samp.run lam [] z.1)).eval w →
          z.2 ∈ Rec lam (Samp.run lam [] z.1) w)) :
    ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyBounded s → (∀ lam, s₀ lam ≤ s lam) →
      ∀ zf : ℕ → List Bool → List Bool,
        PolyTimeOn (ι := ℕ × List Bool) (fun z => [unary z.1, z.2]) (fun z => zf z.1 z.2) →
        CompClose (I := fun _ => Unit)
          (Ω₀ := fun lam => (Fin (Samp.coins lam) → Bool) × (Fin (κ lam) → Bool) ×
            (Fin (O.coins lam (nin lam) (s lam + nout lam)) → Bool))
          (Ω₁ := fun lam => (Fin (Samp.coins lam) → Bool) × (Fin (κ lam) → Bool) ×
            (Fin (O.coins lam (nin lam) (s lam + nout lam)) → Bool))
          (fun _ _ => unifW _)
          (fun lam _ ω => QAdvFew.PoQOracle.tup [zf lam (Samp.run lam [] ω.1),
            (O.obf lam (nin lam) (s lam + nout lam)
              (padC (s lam) (P lam (Samp.run lam [] ω.1) ω.2.1)) ω.2.2).code])
          (fun _ _ => unifW _)
          (fun lam _ ω => QAdvFew.PoQOracle.tup [zf lam (Samp.run lam [] ω.1),
            (O.obf lam (nin lam) (s lam + nout lam)
              (padC (s lam) (P0 lam (Samp.run lam [] ω.1))) ω.2.2).code])
          δ := by sorry

end NoisyOWMPC
