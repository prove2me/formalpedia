-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_4
-- name    : OptTwoSrcExt.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:38:21.69207+00:00
-- url     : https://prove2.me/theorems/5847e843-0955-4cc1-b46e-5b2e6721aba5
-- title:
--   Theorem 3.4 — linear output, exponential error, rank $O_\delta(n)$ and inner-product form
-- statement:
--   Fix $0<\delta\le1$. There are positive constants $c_\delta,a_\delta,C_\delta$ and a deterministic polynomial-time family $\mathrm{Ext}_n:\{0,1\}^n\times\{0,1\}^n\to\mathbb F_2^{m(n)}$ with $m(n)\ge c_\delta n$, defined at every length $n\ge1$, such that:
--
--   1. for independent sources $X,Y$ on $\{0,1\}^n$ with $H_\infty(X),H_\infty(Y)\ge\delta n$,
--   $$\Delta\big(\mathrm{Ext}_n(X,Y),U_{m(n)}\big)\le2^{-a_\delta n};$$
--   2. for every $\beta\in\mathbb F_2^{m(n)}\setminus\{0\}$, the $2^n\times2^n$ matrix of $(x,y)\mapsto\beta\cdot\mathrm{Ext}_n(x,y)$ has $\mathbb F_2$-rank at most $C_\delta n$;
--   3. there are an explicit field $\mathbb F_n=\mathbb F_{2^{\ell(n)}}$ with $a'n\le\ell(n)\le A'n$, an integer $R$ independent of $n$, explicit maps $G_L,G_R:\{0,1\}^n\to\mathbb F_n^R$ and a surjective $\mathbb F_2$-linear map $\pi_n:\mathbb F_n\to\mathbb F_2^{m(n)}$ with
--   $$\mathrm{Ext}_n(x,y)=\pi_n\big(\langle G_L(x),G_R(y)\rangle_{\mathbb F_n}\big)=\pi_n\Big(\sum_{r=1}^R G_L(x)_rG_R(y)_r\Big).\tag{3.4}$$
--
--   So each encoding has $R\ell(n)=O_\delta(n)$ bits. This is the linear-output, exponentially small error two-source extractor for every constant rate that the later non-malleable constructions start from.
--
--   **Formalization Note** "Deterministic polynomial-time" and "explicit" are one `LowErrExt.IsPolyTime` machine each ($\mathrm{Ext}$, the field construction, $G_L$, $G_R$), working for all $n$, chosen after $\delta$ and the constants. $\Theta_\delta(n)$ is $a'n\le\ell\le A'n$ with $0<a'\le A'$ chosen before $n$. Outputs are read with the published `machineVec`, ranks with the published `rank2`. The field is the explicit `BinField`. The closing pointer to Corollary 3.9 is not a claim of this theorem.
--
--   Differences from the source:
--   - reading: explicit maps G_L, G_R into a field F_n = F_{2^{ℓ(n)}} → G_L, G_R computed by polynomial-time machines whose ℓ-bit blocks are read in the power basis of 𝔽₂[X]/(P_ℓ), P_ℓ printed by a polynomial-time field-construction machine; reason: a field given only up to isomorphism would make "explicit" empty; the paper constructs fields deterministically (§2.2, p.18; §3.2.1, p.36)
--   - encoding: ℓ(n) = Θ_δ(n), R = O_δ(1), deterministic polynomial-time family → a′n ≤ ℓ ≤ A′n and one R, all chosen before n; one IsPolyTime machine for all n on inputs [x, y]; reason: asymptotic notation with constants depending on δ only
--   - encoding: independent sources X, Y with H∞(X), H∞(Y) ⩾ δn → arbitrary probability mass functions on {0,1}ⁿ with minEntropy ≥ δn, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.4, p.31 (PDF p.33); "at every positive length", p.34 (PDF p.36)

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

/-- **Theorem 3.4 (Linear output and exponential error).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.4, printed p.31 (PDF p.33): "Fix 0 < δ ⩽ 1.
There are positive constants cδ, aδ, Cδ and a deterministic polynomial-time family
Extn : {0, 1}^n × {0, 1}^n → F_2^{m(n)}, m(n) ⩾ cδn, such that independent sources X, Y with
H∞(X), H∞(Y) ⩾ δn satisfy ∆(Extn(X, Y), Um(n)) ⩽ 2^{−aδn}. For every β ∈ F_2^{m(n)} \ {0},
rank2((x, y) ↦ β · Extn(x, y)) ⩽ Cδn. In addition, there are a field Fn = F_{2^{ℓ(n)}} with
ℓ(n) = Θδ(n), an integer R = Oδ(1), explicit maps GL, GR : {0, 1}^n → Fn^R, and a surjective
binary-linear map πn : Fn → F_2^{m(n)} such that Extn(x, y) = πn(⟨GL(x), GR(y)⟩_{Fn}). (3.4)"
Printed p.34 (PDF p.36): "This completes Theorem 3.4 at every positive length."

For `0 < δ ≤ 1` there are `c, a, C > 0`, constants `0 < a' ≤ A'`, an integer `R`, and
polynomial-time machines `F` (the family `Ext_n(x, y) = F [x, y]`), `Pm` (field construction) and
`Lenc`, `Renc` (the encodings `G_L(x) = Lenc [x]`, `G_R(y) = Renc [y]`) such that for every `n ≥ 1` there are
`m ≥ cn` and `ℓ` with `a'n ≤ ℓ ≤ A'n` for which
1. `Pm` constructs `F_n = 𝔽_{2^ℓ}` (`IsFieldPolyAt Pm ℓ`);
2. `Ext_n` outputs exactly `m` bits on `n`-bit inputs;
3. `Δ(Ext_n(X, Y), U_m) ≤ 2^{−an}` for independent `X, Y` on `{0,1}ⁿ` with `H∞ ≥ δn`;
4. for every `β ≠ 0`, `rank₂((x, y) ↦ β · Ext_n(x, y)) ≤ Cn`;
5. `G_L, G_R` output exactly `Rℓ` bits (`R` elements of `F_n`), and some surjective `𝔽₂`-linear
   `π_n : F_n → 𝔽₂^m` has `Ext_n(x, y) = π_n(Σ_{r<R} G_L(x)_r G_R(y)_r)` for all `x, y`.

**Formalization Note.** "Deterministic polynomial-time family" and "explicit" are one
`LowErrExt.IsPolyTime` machine each, for all `n`, chosen after `δ` and the constants; inputs are the
bit strings (`List.ofFn`), outputs are read with the published `machineVec`. `F_n` is the explicit
field `BinField Pm ℓ` with elements written in its power basis (`eltsOfBits`). `Θ_δ(n)` is
`a'n ≤ ℓ ≤ A'n` and `O_δ(1)` is one `R` for all `n`, both chosen before `n`. `rank₂` is the published
`OptTwoSrcExt.rank2` of the full `2ⁿ × 2ⁿ` table. Sources are arbitrary probability mass functions.
The closing pointer to Corollary 3.9 is not a claim of this theorem. -/
theorem theorem_3_4 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c a C : ℝ, 0 < c ∧ 0 < a ∧ 0 < C ∧ ∃ a' A' : ℝ, 0 < a' ∧ a' ≤ A' ∧ ∃ R : ℕ,
      ∃ F Pm Lenc Renc : List (List Bool) → List Bool,
        IsPolyTime F ∧ IsPolyTime Pm ∧ IsPolyTime Lenc ∧ IsPolyTime Renc ∧
        ∀ n : ℕ, 1 ≤ n → ∃ m ℓ : ℕ, c * n ≤ m ∧ a' * n ≤ ℓ ∧ (ℓ : ℝ) ≤ A' * n ∧
          IsFieldPolyAt Pm ℓ ∧
          (∀ x y : Fin n → Bool, (F [List.ofFn x, List.ofFn y]).length = m) ∧
          (∀ X Y : PMF (Fin n → Bool), δ * n ≤ minEntropy X → δ * n ≤ minEntropy Y →
            statDist ((indepPair X Y).map fun p => machineVec F m [List.ofFn p.1, List.ofFn p.2])
              (PMF.uniformOfFintype (Fin m → ZMod 2)) ≤ (2 : ℝ) ^ (-(a * n))) ∧
          (∀ β : Fin m → ZMod 2, β ≠ 0 →
            (rank2 (fun x y : Fin n → Bool =>
              dotF2 β (machineVec F m [List.ofFn x, List.ofFn y])) : ℝ) ≤ C * n) ∧
          (∀ x : Fin n → Bool, (Lenc [List.ofFn x]).length = R * ℓ) ∧
          (∀ y : Fin n → Bool, (Renc [List.ofFn y]).length = R * ℓ) ∧
          ∃ π : BinField Pm ℓ →ₗ[ZMod 2] (Fin m → ZMod 2), Function.Surjective π ∧
            ∀ x y : Fin n → Bool, machineVec F m [List.ofFn x, List.ofFn y] =
              π (∑ r : Fin R, eltsOfBits Pm ℓ R (Lenc [List.ofFn x]) r *
                eltsOfBits Pm ℓ R (Renc [List.ofFn y]) r) := by sorry

end OptTwoSrcExt.Supplement
