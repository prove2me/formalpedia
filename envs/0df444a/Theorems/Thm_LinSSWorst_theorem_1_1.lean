-- Prove2me | Theorems.Thm_LinSSWorst_theorem_1_1
-- name    : LinSSWorst.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:34.093221+00:00
-- url     : https://prove2.me/theorems/f90669c6-84c8-4b2b-9f99-3c76bcd229ef
-- title:
--   Theorem 1.1 (Main theorem) — linear schemes with maximal share length $2^{\lceil n/2\rceil-1}+1$ over every finite field (corrected: f(0ⁿ) = 0, as in Definition A.1)
-- statement:
--   Let $n\ge 0$ and let $f:\{0,1\}^n\to\{0,1\}$ be an $n$-party access structure, i.e. monotone with $f(0^n)=0$. Then:
--   1. for every finite field $F$ there is a linear secret-sharing scheme $\Pi:F^{1+\ell_r}\to F^{\ell_1+\cdots+\ell_n}$ over $F$ that realizes $f$ and in which every party holds at most
--   $$\ell_i\le 2^{\lceil n/2\rceil-1}+1$$
--   field elements;
--   2. over $\mathbb F_2$ there is such a scheme in which every party's share size $\log_2|\mathbb F_2^{\ell_i}|$ is at most $2^{\lceil n/2\rceil-1}+1$ bits.
--
--   Combined with the counting lower bound of Babai, Gál and Wigderson, this shows that the worst-case exponent of linear secret sharing is exactly $1/2$.
--
--   **Formalization Note** The field ranges over every universe. $\lceil n/2\rceil-1$ is `(n + 1) / 2 - 1` in `ℕ`; at $n=0$ there are no parties. $\mathbb F_2$ is `ZMod 2`, and the share size is `Real.logb 2` of the cardinality of `Fin (ℓ i) → ZMod 2`.
--
--   Differences from the source:
--   - correction: "every monotone function f : {0,1}^n → {0,1}" → every access structure (monotone with f(0ⁿ) = 0, `IsAccessStructure f`); reason: the constant function f ≡ 1 is monotone and no scheme realizes it: correctness at x = 0ⁿ needs one value Recon_{0ⁿ}(()) equal to every secret s ∈ F, impossible since |F| ≥ 2; the correction is the paper's own Definition A.1, also assumed by Theorem 3.2
--   - reading: "with maximal share length of 2^{⌈n/2⌉−1} + 1 field elements" → every ℓ_i ≤ 2^{⌈n/2⌉−1} + 1; reason: the abstract (p.1) says "at most"; padding shares with zero coordinates makes the two readings equivalent
--   - encoding: ⌈n/2⌉ − 1 → `(n + 1) / 2 - 1` in ℕ, all n including n = 0; reason: (n + 1) / 2 = ⌈n/2⌉ for every n, the subtraction is exact for n ≥ 1, and at n = 0 the bound quantifies over no party
--   - encoding: F^{1+ℓ_r} → `F × (Fin ℓr → F)`, F^{ℓ_1+⋯+ℓ_n} → `(i : Fin n) → Fin (ℓ i) → F`; reason: canonical F-linear equivalences
--   - encoding: {0,1}ⁿ → `Fin n → Bool`; "identical distributions over uniform r" → equal push-forwards of `PMF.uniformOfFintype`; reason: same objects
--   - encoding: F₂; share size log |S_j| in bits, "the maximal share size is X bits" → `ZMod 2`; every `Real.logb 2 (Fintype.card (Fin (ℓ i) → ZMod 2))` ≤ X, in a second existential; reason: log₂ |F₂^{ℓ_i}| = ℓ_i, so a witness of this clause also has ℓ_i ≤ X and nothing is lost by the separate existential; ≤ is the reading above
--   - encoding: every finite field F → `F : Type*`; reason: Lean convention; every universe holds the same fields
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_LinSSWorst_Realizes

namespace LinSSWorst

/-- **Theorem 1.1 (Main theorem)**, p.4, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…),
corrected to access structures (`f(0ⁿ) = 0`, Definition A.1). For every `n` and every `n`-party
access structure `f`:
1. for every finite field `F` there is a linear secret-sharing scheme over `F` (Definition A.3:
   an `F`-linear map `F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n}`) that realizes `f` and in which every party's
   share length `ℓ_i` is at most `2^{⌈n/2⌉-1} + 1` field elements;
2. over `F₂` there is such a scheme in which every party's share size `log₂ |F₂^{ℓ_i}|` is at most
   `2^{⌈n/2⌉-1} + 1` bits.

**Formalization Note.** The printed sentence says "every monotone function"; the constant-true
function is monotone and no scheme realizes it (correctness at the empty coalition would need one
value of the empty view equal to every secret), so the statement is restricted to access
structures, as in Definition A.1 and Theorem 3.2. `⌈n/2⌉ - 1` is `(n + 1) / 2 - 1` in `ℕ`; at
`n = 0` there are no parties and the bound is vacuous. "Maximal share length of X" is read as
`ℓ_i ≤ X` for every party (abstract: "at most"). `F₂` is `ZMod 2`; log is base two (§2.1). -/
theorem theorem_1_1 (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : IsAccessStructure f) :
    (∀ (F : Type*) [Field F] [Fintype F],
      ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
        (scheme : (F × (Fin ℓr → F)) →ₗ[F] ((i : Fin n) → Fin (ℓ i) → F)),
        Realizes f scheme ∧ ∀ i, ℓ i ≤ 2 ^ ((n + 1) / 2 - 1) + 1) ∧
    (∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
        (scheme : (ZMod 2 × (Fin ℓr → ZMod 2)) →ₗ[ZMod 2] ((i : Fin n) → Fin (ℓ i) → ZMod 2)),
        Realizes f scheme ∧
          ∀ i, Real.logb 2 (Fintype.card (Fin (ℓ i) → ZMod 2)) ≤
            ((2 ^ ((n + 1) / 2 - 1) + 1 : ℕ) : ℝ)) := by sorry

end LinSSWorst
