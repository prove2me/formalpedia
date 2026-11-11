-- Prove2me | Theorems.Thm_GoldProxGap_corollary_5_2
-- name    : GoldProxGap.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:41.692263+00:00
-- url     : https://prove2.me/theorems/989b269d-5e07-408e-97ee-3a326b203b16
-- title:
--   Corollary 5.2 — dense additive domains: $2^{e_c(\log_2N)^2-O_c(\log N)}$ codewords and nonzero exceptional challenges at $T/N=1/2-\Theta_c(N^{-\theta_c})$ for rate-$1/4$ Reed–Solomon codes
-- statement:
--   **Corollary 5.2 (Dense additive domains).** Fix an integer $c\ge0$ and put $\theta_c=\min\{1/4,1/(c+1)\}$ and $e_c=\theta_c(1-2\theta_c)$. For every sufficiently large $d$ and every additive $d$-space $D\subseteq\mathbb B=\mathbb F_{2^{d+c}}$, with $N=2^d$, there is an agreement $T$ with
--   $$
--   \frac TN=\frac12-\Theta_c\bigl(N^{-\theta_c}\bigr)
--   $$
--   such that, for the Reed–Solomon code of message length $N/4$ on $D$:
--   1. **Lists.** Some word $D\to\mathbb B$ has at least $2^{e_c(\log_2N)^2-O_c(\log N)}$ codewords at agreement $T$.
--   2. **Exceptional challenges.** Over some extension $\mathbb F\supseteq\mathbb B$ with $\log_2|\mathbb F|=e_c(\log_2N)^2+O_c(\log N)$, some pair $f,g$ with $\mathrm{CA}_{N/4}(f,g)=N/4$ has at least $2^{e_c(\log_2N)^2-O_c(\log N)}$ distinct nonzero exceptional challenges at agreement $T$, a fraction $\Omega_c(N^{-1+2\theta_c})$ of $\mathbb F$.
--
--   In particular, for $c\le3$ the list size and the exceptional count are at least $N^{(1/8-o(1))\log_2N}$, the Johnson deficit is $\Theta(N^{-1/4})$, and the exceptional probability is $\Omega(N^{-1/2})$.
--
--   The Johnson threshold for rate $1/4$ is agreement $N/2$; the corollary shows that on dense binary additive domains the decoding list is superpolynomial and no bound of the form $\mathrm{poly}(N)/|\mathbb F|$ on exceptional challenges can hold for any agreement below Johnson at the stated gap.
--
--   **Formalization Note** Each asymptotic symbol is an explicit constant depending on $c$ only, fixed before $d$, $\mathbb B$ and $D$: $0<a_1\le a_2$ with $a_1N^{-\theta_c}\le\frac12-\frac TN\le a_2N^{-\theta_c}$; $C_1$ and $C_3$ in the two count bounds; $C_2$ with $|\log_2|\mathbb F|-e_c(\log_2N)^2|\le C_2\log_2N$; $c_4>0$ with $|\mathrm{Bad}_T(f,g)\setminus\{0\}|/|\mathbb F|\ge c_4N^{-1+2\theta_c}$; and a threshold $d_0$. $\mathbb B$ ranges over all fields with $2^{d+c}$ elements, $D$ over additive subgroups with $2^d$ elements, and $\mathbb F$ is some finite field with an algebra map from $\mathbb B$; the code over $\mathbb F$ lives on the image of $D$.
--
--   Differences from the source:
--   - encoding: Θ_c, O_c, Ω_c and "every sufficiently large d" → real constants a₁ ≤ a₂ (a₁ > 0), C₁, C₂, C₃, c₄ > 0 and a threshold d₀, chosen for each c before d, B and D; log N as log₂ N; reason: the paper's convention (p.19): implicit constants depend only on the subscript, the code length tends to infinity
--   - encoding: D an additive d-space in B = F_{2^{d+c}}, an extension F ⊇ B → every field B with 2^{d+c} elements, every additive subgroup D with 2^d elements, some finite field F with Algebra B F, the code over F on the image of D; reason: finite fields of the same size are isomorphic; additive subgroups in characteristic two are F₂-subspaces
--   - encoding: list size; number of distinct nonzero exceptional challenges → the number of codewords D → B in the decoding list; |Bad_T(f, g) \ {0}|; reason: Definitions 3.3 and 3.4
--   - reading: "In particular, for c ≤ 3 …" → no separate conjunct; reason: for c ≤ 3, θ_c = 1/4 and e_c = 1/8, and the sentence is the c ≤ 3 instance of items 1–2 and of the Θ_c clause
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Corollary 5.2, p.35 (printed = PDF page 35)

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Corollary 5.2 (Dense additive domains)**, p.35. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Fix an integer c ≥ 0, and put θ_c = min{1/4, 1/(c + 1)} and e_c = θ_c(1 − 2θ_c). For every
sufficiently large d and every additive d-space D ⊆ B = F_{2^{d+c}}, with N = 2^d, there is an
agreement T with T/N = 1/2 − Θ_c(N^{−θ_c}) such that the following hold for the code of message
length N/4 on D.
1. Lists. Some word over B has at least 2^{e_c(log₂ N)² − O_c(log N)} codewords at agreement T.
2. Exceptional challenges. Over some extension F ⊇ B with log₂ |F| = e_c(log₂ N)² + O_c(log N),
some pair with CA_{N/4}(f, g) = N/4 has at least 2^{e_c(log₂ N)² − O_c(log N)} distinct nonzero
exceptional challenges at agreement T, a fraction Ω_c(N^{−1+2θ_c}) of F.
In particular, for c ≤ 3 the list size and the exceptional count are at least
N^{(1/8−o(1)) log₂ N}, the Johnson deficit is Θ(N^{−1/4}), and the exceptional probability is
Ω(N^{−1/2}). The decoding list is over an alphabet of size 2^c N."

**Formalization Note.**
* Asymptotic notation (convention, p.19: "Subscripts on asymptotic notation indicate parameters
  on which the implicit constants may depend; the variable tending to infinity is the code
  length"): for each `c` there are real constants `0 < a₁ ≤ a₂`, `C₁`, `C₂`, `C₃`, `c₄ > 0` and a
  threshold `d₀`, all chosen before `d`, `B` and `D`. `Θ_c` is two-sided, the field size `=` with
  `O_c` is two-sided (`|log₂|F| − e_c(log₂N)²| ≤ C₂ log₂ N`), the counts are lower bounds.
  `log N` is `log₂ N` (`Real.logb 2`), which changes `O_c(log N)` by a constant factor only.
* `B = F_{2^{d+c}}` is every field with `2^{d+c}` elements; an additive `d`-space is an additive
  subgroup with `2^d` elements. `F ⊇ B` is some finite field (in `Type`) with `Algebra B F`; the
  code over `F` lives on the image of `D` in `F`.
* Item 1 counts codewords over `B` (functions `D → B`), item 2 the set `Bad_T(f, g) \ {0}`. The
  same `T` serves both items.
* The "In particular" sentence is the `c ≤ 3` instance of these clauses (`θ_c = 1/4`,
  `e_c = 1/8`), and is not a separate conjunct. -/
theorem corollary_5_2 (c : ℕ) :
    let θ : ℝ := min (1 / 4) (1 / ((c : ℝ) + 1))
    let e : ℝ := θ * (1 - 2 * θ)
    ∃ a₁ a₂ C₁ C₂ C₃ c₄ : ℝ, 0 < a₁ ∧ a₁ ≤ a₂ ∧ 0 < c₄ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ (B : Type) [Field B] [Fintype B], Fintype.card B = 2 ^ (d + c) →
      ∀ D : AddSubgroup B, Nat.card D = 2 ^ d →
        let N : ℕ := 2 ^ d
        let Dom : Finset B := domainFinset D
        ∃ T : ℕ,
          a₁ * (N : ℝ) ^ (-θ) ≤ 1 / 2 - (T : ℝ) / N ∧ 1 / 2 - (T : ℝ) / N ≤ a₂ * (N : ℝ) ^ (-θ) ∧
          (∃ w : Dom → B, (2 : ℝ) ^ (e * (Real.logb 2 N) ^ 2 - C₁ * Real.logb 2 N) ≤
            ((decodingList Dom (N / 4) T w).card : ℝ)) ∧
          ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : Algebra B F),
            |Real.logb 2 (Fintype.card F) - e * (Real.logb 2 N) ^ 2| ≤ C₂ * Real.logb 2 N ∧
            ∃ f g : pushDomain F Dom → F,
              CA (pushDomain F Dom) (N / 4) f g = N / 4 ∧
              (2 : ℝ) ^ (e * (Real.logb 2 N) ^ 2 - C₃ * Real.logb 2 N) ≤
                (((Bad (pushDomain F Dom) (N / 4) T f g).erase 0).card : ℝ) ∧
              c₄ * (N : ℝ) ^ (-1 + 2 * θ) ≤
                (((Bad (pushDomain F Dom) (N / 4) T f g).erase 0).card : ℝ) /
                  (Fintype.card F : ℝ) := by sorry

end GoldProxGap
