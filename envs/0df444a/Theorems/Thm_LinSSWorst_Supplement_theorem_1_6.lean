-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_1_6
-- name    : LinSSWorst.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:47:49.816225+00:00
-- url     : https://prove2.me/theorems/ee47459b-d4b9-4663-8e14-ccd709c55d80
-- title:
--   Theorem 1.6 (Quadratic schemes beyond the linear exponent) — total share size $\le 2^{0.4994n+o(n)}$, quadratic exponent $\le0.4994<1/2=S_\ell$ (corrected: f(0ⁿ) = 0, as in Definition A.1)
-- statement:
--   There is a function $g(n)=o(n)$ such that every $n$-party access structure $f$ can be realized by a secret-sharing scheme with quadratic sharing and reconstruction with total share size at most
--   $$2^{0.4994\,n+g(n)}.$$
--   Consequently the quadratic secret-sharing exponent is at most $0.4994$, while the linear exponent is $S_\ell=\tfrac12$: the quadratic exponent is strictly smaller than the linear one.
--
--   This separates linear schemes from schemes whose sharing and reconstruction have degree two.
--
--   **Formalization Note** Quadratic schemes are over $\mathbb F_2$ with one-bit secrets: every share coordinate is a polynomial of total degree at most $2$ in the secret and the randomness, and every authorized coalition has a reconstruction polynomial of total degree at most $2$. Total share size is $\sum_i\ell_i$ bits.
--
--   Differences from the source:
--   - correction: every monotone function f : {0,1}^n → {0,1} → every n-party access structure (monotone and f(0ⁿ) = 0); reason: f ≡ 1 is monotone and no scheme realizes it: the empty coalition would have to reconstruct both secrets from the same empty view; the paper's own Definition A.1
--   - reading: total share size at most 2^{0.4994n+o(n)} → ∃ g =o[atTop] n, chosen before n and f, with Σ ℓ_i ≤ 2^{0.4994n + g(n)}; reason: the standard meaning of a uniform o(n) upper bound
--   - reading: quadratic schemes and S_ℓ, field unspecified → quadratic and linear schemes over F₂ with one-bit secrets; reason: App. A.1: exponents are for one-bit secrets, and [BOP21] schemes compute over the field of the secret
--   - encoding: 0.4994 < 1/2 = S_ℓ; strictly smaller → quadExponent ≤ 0.4994 ∧ linExponent = 1/2; reason: 0.4994 < 1/2 is a numeral inequality; the strict separation follows
--   - encoding: exponents as real numbers → infimum in ℝ≥0∞, logarithm, maximum and limsup in EReal; reason: complete-lattice values avoid junk defaults
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 1.6, p.6; definition of quadratic schemes, p.5; exponents App. A.1, p.30

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_Supplement_RealizesQuad
import Definitions.Def_LinSSWorst_Supplement_exponentOf

open Asymptotics

namespace LinSSWorst.Supplement

/-- **Theorem 1.6 (Quadratic schemes beyond the linear exponent)**, p.6, from O. Nir, *Resolving the
Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02,
sha256 5521cfdb…), corrected to access structures (`f(0ⁿ) = 0`, Definition A.1). There is a function
`g(n) = o(n)` such that every `n`-party access structure `f` can be realized by a secret-sharing scheme
with quadratic sharing and reconstruction (over `F₂`, one-bit secrets) with total share size at most
`2^{0.4994 n + g(n)}`. Hence the quadratic secret-sharing exponent is at most `0.4994 < 1/2 = S_ℓ`.

**Formalization Note.** As in Theorem 1.5, "every monotone function" is restricted to access structures
(no scheme realizes the constant-true function). A quadratic scheme (`RealizesQuad`) has every share
coordinate a polynomial of total degree `≤ 2` in the secret `s ∈ F₂` and the random `r ∈ F₂^{ℓ_r}`, and a
reconstruction polynomial of total degree `≤ 2` for every authorized coalition; its total share size is
`Σ_i ℓ_i` bits. `o(n)` is one function `g =o[atTop] n`, chosen before `n` and `f`. The exponents are the
`EReal`-valued `lim sup`s of App. A.1 (`quadExponent`; `linExponent` over `F₂`). `0.4994 < 1/2` is
arithmetic and is not restated. -/
theorem theorem_1_6 :
    (∃ g : ℕ → ℝ, g =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), IsAccessStructure f →
        ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
          (sh : (i : Fin n) → Fin (ℓ i) → MvPolynomial (Option (Fin ℓr)) (ZMod 2)),
          RealizesQuad f sh ∧
            ((∑ i, ℓ i : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((0.4994 : ℝ) * n + g n)) ∧
    quadExponent ≤ ((0.4994 : ℝ) : EReal) ∧
    linExponent = ((1 / 2 : ℝ) : EReal) := by sorry

end LinSSWorst.Supplement
