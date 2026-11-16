-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_5_4
-- name    : GoldProxGap.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:47:37.608456+00:00
-- url     : https://prove2.me/theorems/bc80ee35-8898-436f-ae8b-9424e87e312e
-- title:
--   Theorem 5.4 — no fixed polynomial exceptional bound below Johnson
-- statement:
--   **Theorem 5.4 (No fixed polynomial exceptional bound below Johnson).** Fix an agreement fraction $1/4<a<1/2$ and a proposed polynomial bound $C_0N^b$, where $C_0,b>0$. For arbitrarily large code lengths $N$ there are a binary field $\mathbb F$ (a finite field of characteristic two), a rate-$1/4$ Reed–Solomon code of length $N$ over $\mathbb F$ (evaluation on a set $D\subseteq\mathbb F$ of $N$ points, message length $N/4$), and two received words $f,g:D\to\mathbb F$ such that
--
--   1. the two words have common agreement exactly $N/4$: $\mathrm{CA}_{N/4}(f,g)=N/4$;
--   2. for more than $C_0N^b$ distinct challenges $z\in\mathbb F$, the combination $f+zg$ agrees with a codeword on at least $aN$ positions:
--   $$
--   \#\{z\in\mathbb F:\ \mathrm{agr}_{N/4}(f+zg)\ge aN\}\ >\ C_0N^b .
--   $$
--
--   The field size is polynomial in $N$, with an exponent that depends only on $b$: there is $E$, depending only on $b$, with $|\mathbb F|\le N^E$.
--
--   At rate $1/4$ the Johnson agreement is $N/2$; the theorem rules out any proximity-gap statement that would bound the number of exceptional challenges below Johnson by a fixed polynomial in $N$ over polynomial-size binary fields.
--
--   **Formalization Note** Quantifier order: for every $b>0$ there is $E\in\mathbb N$ such that for every $a\in(1/4,1/2)$, every $C_0>0$ and every $N_0$ there is $N\ge N_0$ with $4\mid N$ and the stated field, domain and pair. $N^b$ is a real power.
--
--   Differences from the source:
--   - reading: for arbitrarily large code lengths N … The field size is polynomial in N, with an exponent that depends only on b → ∀ b > 0, ∃ E : ℕ, ∀ a ∈ (1/4, 1/2), ∀ C₀ > 0, ∀ N₀, ∃ N ≥ N₀ with |F| ≤ N^E; reason: 'arbitrarily large' is ∀ N₀ ∃ N ≥ N₀; a bound C·N^{E'} with a constant C becomes N^{E'+1} once N ≥ C, and N may be taken that large, so the exponent form is the same claim
--   - encoding: a rate-1/4 Reed–Solomon code over a binary field F → a finite field F with ringChar F = 2, a set D : Finset F with |D| = N and 4 ∣ N, and the code C_{N/4}(D; F); reason: rate 1/4 means message length N/4 on N evaluation points
--   - encoding: more than C₀N^b distinct challenges z ∈ F with agreement at least aN → C₀·N^b < #{z ∈ F : aN ≤ agr_{N/4}(f + z g)} in ℝ; reason: agr is the maximum agreement with a codeword
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 5.4, pp.36–37

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 5.4 (No fixed polynomial exceptional bound below Johnson)**, pp.36–37. Dao,
Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*,
STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Fix an agreement fraction 1/4 < a < 1/2 and a proposed polynomial bound C₀N^b, where C₀, b > 0.
For arbitrarily large code lengths N, there is a rate-1/4 Reed–Solomon code over a binary field F
and two received words f, g with the following properties:
1. The two words have common agreement exactly N/4. That is, the largest number of positions on
which f and g simultaneously match a pair of codewords is N/4.
2. For more than C₀N^b distinct challenges z ∈ F, the combination f + zg agrees with a codeword
on at least aN positions.
The field size is polynomial in N, with an exponent that depends only on b."

**Formalization Note.**
* Quantifiers: for every `b > 0` there is an exponent `E : ℕ` (depending only on `b`) such that
  for every `a ∈ (1/4, 1/2)`, every `C₀ > 0` and every `N₀` there is a code length `N ≥ N₀`
  ("arbitrarily large") with the stated code, field and pair.
* A rate-`1/4` Reed–Solomon code of length `N` over `F` is `C_{N/4}(D; F)` for a set `D ⊆ F` of
  `N` points, with `4 ∣ N`. A binary field is a finite field of characteristic two.
* "Field size polynomial in N with exponent depending only on b" is `|F| ≤ N^E`.
* Item 2 counts the challenges `z ∈ F` with `aN ≤ agr_{N/4}(f + z g)` (a real comparison), and
  requires more than `C₀N^b` of them (`N^b` is `Real.rpow`). -/
theorem theorem_5_4 (b : ℝ) (hb : 0 < b) :
    ∃ E : ℕ, ∀ a : ℝ, 1 / 4 < a → a < 1 / 2 → ∀ C₀ : ℝ, 0 < C₀ → ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 4 ∣ N ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), ringChar F = 2 ∧ Fintype.card F ≤ N ^ E ∧
          ∃ D : Finset F, D.card = N ∧ ∃ f g : D → F,
            CA D (N / 4) f g = N / 4 ∧
            C₀ * (N : ℝ) ^ b <
              ((Finset.univ.filter
                (fun z : F => a * (N : ℝ) ≤ (agr D (N / 4) (f + z • g) : ℝ))).card : ℝ) := by sorry

end GoldProxGap.Supplement
