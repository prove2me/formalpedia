-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_22
-- name    : OptTwoSrcExt.Supplement.theorem_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:38:53.243648+00:00
-- url     : https://prove2.me/theorems/d49a9a87-ef35-44e8-b7c0-e5f7dc4486af
-- title:
--   Theorem 3.22 — constant-rate sumset extraction with rank $O_\delta(n)$ and separated encodings
-- statement:
--   For every fixed $0<\delta\le1$ there are positive constants $c_\delta,e_\delta,C_\delta$ such that, for all sufficiently large $n$, a uniformly polynomial-time computable map $\mathrm{Ext}_n:\mathbb F_2^n\to\mathbb F_2^{m_n}$ with $m_n\ge c_\delta n$ satisfies:
--
--   1. for every independent pair $X,Y$ on $\mathbb F_2^n$ with $H_\infty(X),H_\infty(Y)\ge\delta n$,
--   $$\Delta\big(\mathrm{Ext}_n(X+Y),U_{m_n}\big)\le2^{-e_\delta n};$$
--   2. for every nonzero output functional $\lambda$, the matrix $[\lambda\cdot\mathrm{Ext}_n(x+y)]_{x,y\in\mathbb F_2^n}$ has rank over $\mathbb F_2$ at most $C_\delta n$;
--   3. more precisely, $\mathrm{Ext}_n(x+y)=\pi\big(\sum_{r=1}^R G_L(x)_rG_R(y)_r\big)$ for a surjective $\mathbb F_2$-linear projection $\pi:\mathbb F_{2^{\ell}}\to\mathbb F_2^{m_n}$, a constant $R$ (a constant number of separated products) and a field of binary dimension $\ell=\Theta_\delta(n)$, with explicit separated encodings $G_L,G_R$ of total binary length $R\ell=O_\delta(n)$.
--
--   "Uniformly polynomial-time" is for each fixed rate: the algorithm's constants are fixed independently of the source distributions and of $n$. A sumset extractor sees only $x+y$; this one has linear output, exponential error and low-rank characters, the ingredients of the paper's sumset seed.
--
--   **Formalization Note** One `LowErrExt.IsPolyTime` machine computes $\mathrm{Ext}_n$ for all $n$ (input $z$ as a bit list), and polynomial-time machines construct the field and compute $G_L,G_R$. $\Theta_\delta(n)$ is $a'n\le\ell\le A'n$; $R$, $a'$, $A'$ and the length threshold are chosen before $n$. Ranks are the published `rank2`.
--
--   Differences from the source:
--   - reading: the output is a binary-linear projection of a field-valued expression having a constant number of separated products over a field of binary dimension Θ_δ(n); explicit separated encodings of total binary length O_δ(n) → Ext_n(x + y) = π(Σ_{r<R} G_L(x)_r G_R(y)_r) with π surjective 𝔽₂-linear, R constant, the field BinField Pm ℓ with a′n ≤ ℓ ≤ A′n, G_L, G_R polynomial-time with exactly Rℓ output bits; reason: separation length at most R over the field is Definition 2.12 (p.18); a projection onto 𝔽₂^{m_n} is surjective (the construction's "fixed binary-linear output projection", (3.28), p.42); explicit fields as in §2.2
--   - encoding: uniformly polynomial-time map on 𝔽₂ⁿ; for all sufficiently large n → one IsPolyTime machine on the bit list of z; ∀ n ≥ n₀ with n₀ chosen after δ; reason: same meaning
--   - encoding: independent sources X, Y with H∞(X), H∞(Y) ⩾ δn → arbitrary probability mass functions on 𝔽₂ⁿ with minEntropy ≥ δn, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.22, p.41 (PDF p.43); construction (3.28), p.42 (PDF p.44)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_fourier
import Definitions.Def_OptTwoSrcExt_machineVec
import Definitions.Def_OptTwoSrcExt_Supplement_BinField

open FuzzyExtractors.Hamming LowErrExt OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 3.22 (Constant-rate sumset extraction).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.22, printed p.41 (PDF p.43): "For every fixed
0 < δ ⩽ 1, there are positive constants cδ, eδ, Cδ such that, for all sufficiently large n, a
uniformly polynomial-time computable map Extn : F_2^n → F_2^{mn}, mn ⩾ cδn, satisfies
∆(Extn(X + Y), Umn) ⩽ 2^{−eδn} for every independent pair with H∞(X), H∞(Y) ⩾ δn. For every
nonzero output functional λ, the matrix [λ · Extn(x + y)]_{x,y∈F_2^n} has rank over F2 at most Cδn.
More precisely, the output is a binary-linear projection of a field-valued expression having a
constant number of separated products over a field of binary dimension Θδ(n). Thus explicit
separated encodings of total binary length Oδ(n) are available for its lifted characters. Here
“uniformly polynomial-time” is for each fixed rate: the constants in the algorithm are fixed
independently of the source distributions and of n."

For `0 < δ ≤ 1` there are `c, e, C > 0`, constants `0 < a' ≤ A'`, an integer `R`, a threshold
`n₀` and polynomial-time machines `F` (`Ext_n(z) = F [z]`), `Pm` (field construction) and `Lenc, Renc`
(the separated factors `G_L(x) = Lenc [x]`, `G_R(y) = Renc [y]`) such that for every `n ≥ n₀` there are `m ≥ cn` and `ℓ` with
`a'n ≤ ℓ ≤ A'n` for which
1. `Pm` constructs `𝔽_{2^ℓ}`;
2. `Ext_n` outputs exactly `m` bits on `𝔽₂ⁿ`;
3. `Δ(Ext_n(X + Y), U_m) ≤ 2^{−en}` for independent `X, Y` on `𝔽₂ⁿ` with `H∞ ≥ δn`;
4. for every `λ ≠ 0` the `2ⁿ × 2ⁿ` matrix `[λ · Ext_n(x + y)]` has `𝔽₂`-rank at most `Cn`;
5. `G_L, G_R` output exactly `Rℓ` bits (`R` elements of `𝔽_{2^ℓ}`), and some surjective
   `𝔽₂`-linear `π : 𝔽_{2^ℓ} → 𝔽₂^m` (an output projection, (3.28), p.42) has `Ext_n(x + y) = π(Σ_{r<R} G_L(x)_r G_R(y)_r)` for all `x, y`.

**Formalization Note.** "Uniformly polynomial-time" is one `LowErrExt.IsPolyTime` machine for all
`n`, chosen after `δ`; `𝔽₂ⁿ` is written to it as a bit list (`bitsOfVec`); outputs are read with
`machineVec`. "A constant number of separated products" is the sum of `R` products
`G_L(x)_r G_R(y)_r` (separation length `≤ R`, Definition 2.12, p.18), with `R` and the field-degree
constants chosen before `n`; "binary-linear projection" is read as a surjective `𝔽₂`-linear map
(the construction's "fixed binary-linear output projection", (3.28), printed p.42, PDF p.44); "explicit separated encodings of total binary length `O_δ(n)`" is the
polynomial-time computability of `G_L, G_R` with `Rℓ ≤ RA'n` bits. The field is the explicit
`BinField Pm ℓ`. Sources are arbitrary probability mass functions. -/
theorem theorem_3_22 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c e C : ℝ, 0 < c ∧ 0 < e ∧ 0 < C ∧ ∃ a' A' : ℝ, 0 < a' ∧ a' ≤ A' ∧ ∃ R n₀ : ℕ,
      ∃ F Pm Lenc Renc : List (List Bool) → List Bool,
        IsPolyTime F ∧ IsPolyTime Pm ∧ IsPolyTime Lenc ∧ IsPolyTime Renc ∧
        ∀ n : ℕ, n₀ ≤ n → ∃ m ℓ : ℕ, c * n ≤ m ∧ a' * n ≤ ℓ ∧ (ℓ : ℝ) ≤ A' * n ∧
          IsFieldPolyAt Pm ℓ ∧
          (∀ z : Fin n → ZMod 2, (F [bitsOfVec z]).length = m) ∧
          (∀ X Y : PMF (Fin n → ZMod 2), δ * n ≤ minEntropy X → δ * n ≤ minEntropy Y →
            statDist ((indepPair X Y).map fun p => machineVec F m [bitsOfVec (p.1 + p.2)])
              (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ (2 : ℝ) ^ (-(e * n))) ∧
          (∀ l : Fin m → ZMod 2, l ≠ 0 →
            (rank2 (fun x y : Fin n → ZMod 2 =>
              dotF2 l (machineVec F m [bitsOfVec (x + y)])) : ℝ) ≤ C * n) ∧
          (∀ x : Fin n → ZMod 2, (Lenc [bitsOfVec x]).length = R * ℓ) ∧
          (∀ y : Fin n → ZMod 2, (Renc [bitsOfVec y]).length = R * ℓ) ∧
          ∃ π : BinField Pm ℓ →ₗ[ZMod 2] (Fin m → ZMod 2), Function.Surjective π ∧
            ∀ x y : Fin n → ZMod 2, machineVec F m [bitsOfVec (x + y)] =
              π (∑ r : Fin R, eltsOfBits Pm ℓ R (Lenc [bitsOfVec x]) r *
                eltsOfBits Pm ℓ R (Renc [bitsOfVec y]) r) := by sorry

end OptTwoSrcExt.Supplement
