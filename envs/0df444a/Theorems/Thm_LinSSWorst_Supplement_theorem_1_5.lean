-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_1_5
-- name    : LinSSWorst.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:47:16.515276+00:00
-- url     : https://prove2.me/theorems/fbfcb368-25ed-48ac-84d9-a4cd669ca76c
-- title:
--   Theorem 1.5 (Beyond the linear exponent) — total share size $2^{0.494n+o(n)}$, hence $S\le0.494<1/2=S_\ell$ (corrected: f(0ⁿ) = 0, as in Definition A.1)
-- statement:
--   There is a function $g(n)=o(n)$ such that every $n$-party access structure $f$ can be realized by a secret-sharing scheme for one-bit secrets with total share size at most
--   $$2^{0.494\,n+g(n)}.$$
--   Consequently the secret-sharing exponent satisfies $S\le0.494$, while the linear exponent is $S_\ell=\tfrac12$: the non-linear exponent is strictly smaller than the linear one.
--
--   This is the first unconditional separation between general and linear secret sharing for the worst-case access structure.
--
--   **Formalization Note** Schemes are those of Definition A.2 with $S=$ `Bool`, finite nonempty randomness and finite share domains in `Type`; total share size is $\sum_j\log_2|S_j|$. The exponents are the extended-real $\limsup$s of App. A.1.
--
--   Differences from the source:
--   - correction: every monotone function f : {0,1}^n → {0,1} → every n-party access structure (monotone and f(0ⁿ) = 0); reason: f ≡ 1 is monotone and no scheme realizes it: the empty coalition would have to reconstruct both secrets from the same empty view; the paper's own Definition A.1
--   - reading: total share size 2^{0.494n+o(n)} → ∃ g =o[atTop] n, chosen before n and f, with total share size ≤ 2^{0.494n + g(n)}; reason: the standard meaning of a uniform o(n) upper bound
--   - reading: S_ℓ, the linear exponent → linear exponent of schemes over F₂; reason: App. A.1 defines exponents for one-bit secrets and a linear scheme's secret lies in its field; Theorem 1.1 and Theorem 7.1 with [KW93] give 1/2 over every finite field anyway
--   - encoding: 0.494 < 1/2 = S_ℓ; non-linear exponent strictly smaller → genExponent ≤ 0.494 ∧ linExponent = 1/2; reason: 0.494 < 1/2 is a numeral inequality; the strict separation follows from the two stated facts
--   - encoding: SSize(f) = min over schemes; exponents as real numbers → infimum in ℝ≥0∞, logarithm, maximum and limsup in EReal; reason: complete-lattice values avoid junk defaults; the minimum is attained since finitely many share-size tuples lie below any bound
--   - encoding: R a finite set of random strings, S_j sets → R a nonempty Fintype, σ j Fintypes, in Type; reason: the uniform distribution on R needs R ≠ ∅; finite sets live in Type
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 1.5, p.5; exponents App. A.1, p.30

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_Supplement_RealizesGen
import Definitions.Def_LinSSWorst_Supplement_exponentOf

open Asymptotics

namespace LinSSWorst.Supplement

/-- **Theorem 1.5 (Beyond the linear exponent)**, p.5, from O. Nir, *Resolving the Worst-Case Complexity
of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…),
corrected to access structures (`f(0ⁿ) = 0`, Definition A.1). There is a function `g(n) = o(n)` such that
every `n`-party access structure `f` can be realized by a secret-sharing scheme for one-bit secrets
(Definition A.2) with total share size at most `2^{0.494 n + g(n)}`. Hence `S ≤ 0.494 < 1/2 = S_ℓ`: the
secret-sharing exponent of all access structures is at most `0.494`, and the linear exponent equals `1/2`.

**Formalization Note.** The printed sentence says "every monotone function"; the constant-true function is
monotone and no scheme realizes it (the empty coalition would have to reconstruct, impossible with
`|S| = 2`), so `f` ranges over access structures, as in Definition A.1. `o(n)` is one function
`g =o[atTop] n`, chosen before `n` and `f`. Schemes are maps `Bool × R → Π_j σ j` with `R` a nonempty finite
type and finite share domains, all in `Type`; total share size is `Σ_j log₂ |σ j|`. The exponents `S`
(`genExponent`) and `S_ℓ` (`linExponent`, linear schemes over `F₂`, the field of one-bit secrets) are the
`EReal`-valued `lim sup`s of App. A.1. `0.494 < 1/2` is arithmetic and is not restated. -/
theorem theorem_1_5 :
    (∃ g : ℕ → ℝ, g =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), IsAccessStructure f →
        ∃ (R : Type) (_ : Fintype R) (_ : Nonempty R) (σ : Fin n → Type) (_ : ∀ i, Fintype (σ i))
          (scheme : Bool → R → (i : Fin n) → σ i),
          RealizesGen f scheme ∧
            totalShareSize σ ≤ (2 : ℝ) ^ ((0.494 : ℝ) * n + g n)) ∧
    genExponent ≤ ((0.494 : ℝ) : EReal) ∧
    linExponent = ((1 / 2 : ℝ) : EReal) := by sorry

end LinSSWorst.Supplement
