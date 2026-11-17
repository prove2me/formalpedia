-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_64
-- name    : OptTwoSrcExt.Supplement.theorem_3_64
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:41:20.285987+00:00
-- url     : https://prove2.me/theorems/3f31ae1e-488d-4cac-9534-69bd805d9686
-- title:
--   Theorem 3.64 — fixed-$C$ non-malleable two-source extraction with exponential error
-- statement:
--   Fix an integer $C\ge1$ and $0<\delta\le1$. There are constants $c_{\delta,C},a_{\delta,C},R_{\delta,C}>0$ and a deterministic polynomial-time family $\mathrm{nmExt}:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^m$, specified at every length $n\ge1$, such that $m\ge c_{\delta,C}n$ and:
--
--   1. for independent sources $X,Y$ of min-entropy at least $\delta n$ and every admissible $C$-tuple of separate tamperings $(f_i,g_i)$ (i.e. $\Pr[(f_i(X),g_i(Y))=(X,Y)]=0$),
--   $$\Delta\Big(\big(\mathrm{nmExt}(X,Y),(\mathrm{nmExt}(f_i(X),g_i(Y)))_{i=1}^C\big),\big(U_m,(\mathrm{nmExt}(f_i(X),g_i(Y)))_{i=1}^C\big)\Big)\le2^{-a_{\delta,C}n},$$
--   with no entropy assumption on the tampered images;
--   2. every output character has binary matrix rank at most $R_{\delta,C}n$;
--   3. every output character has explicit separated encodings of length $O_{\delta,C}(n)$: there are explicit $u,v:\{0,1\}^n\to\mathbb F_2^{D}$ with $D\le D'n$ such that every character $\beta\cdot\mathrm{nmExt}(x,y)$ equals $u(x)^{\mathsf T}M_\beta v(y)$ for a matrix $M_\beta$;
--   4. a separately source-strong companion has the same asymptotic output and error parameters: a second deterministic polynomial-time family with output length $m'\ge c'n$ that is separately source strong $C$-non-malleable (Definition 2.3) at entropy $\delta n$ with error $2^{-a'n}$.
--
--   The input rate $\delta$ is arbitrary and is fixed independently of $C$. This is the paper's constant-rate, exponentially small error non-malleable extractor for a fixed number of tamperings.
--
--   **Formalization Note** Each family is one `LowErrExt.IsPolyTime` machine for all $n$, chosen after $C,\delta$ and the constants; $u,v$ are polynomial-time machines with exactly $D$ output bits. The companion's constants $c',a'>0$ are its own. Non-malleability and source strength are the definitions `IsNMExt`, `IsSourceStrongNM` of this supplement.
--
--   Differences from the source:
--   - reading: every output character has explicit separated encodings of length O_{δ,C}(n) → one pair of polynomial-time maps u, v : {0,1}ⁿ → 𝔽₂^D, D ≤ D′n, such that every character is a bilinear form u(x)ᵀ M_β v(y) (common binary features, Definition 2.12); reason: of the two readings (per-character encodings, or one common pair) the stronger is taken; the construction gives it ("trace-dual bases turn each binary output character into an inner product of explicit encodings", p.73)
--   - reading: a separately source-strong companion has the same asymptotic output and error parameters → a second polynomial-time machine with output m′ ≥ c′n, separately source strong C-non-malleable at entropy δn with error 2^{−a′n}, c′, a′ > 0 its own constants; reason: "the same asymptotic parameters" = linear output and exponential error (Corollary 3.65, p.79: output Ω_{δ,C}(k), error 2^{−Ω_{δ,C}(n)})
--   - encoding: independent sources with H∞ ≥ k → arbitrary probability mass functions on {0,1}ⁿ with minEntropy ≥ k, law of the pair = indepPair; reason: published FuzzyExtractors.Hamming / LowErrExt definitions; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.64, p.73 (PDF p.75); "specified at every positive length", p.79 (PDF p.81)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_fourier
import Definitions.Def_OptTwoSrcExt_machineVec
import Definitions.Def_OptTwoSrcExt_Supplement_IsNMExt

open LowErrExt OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 3.64 (Fixed-C non-malleability with exponential error).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.64, printed p.73 (PDF p.75): "Fix an integer
C ⩾ 1 and 0 < δ ⩽ 1. There are constants cδ,C, aδ,C, Rδ,C > 0 and a deterministic polynomial-time
family nmExt : {0, 1}^n × {0, 1}^n → {0, 1}^m such that m ⩾ cδ,Cn and, for independent sources of
min-entropy at least k ⩾ δn and every admissible C-tuple of separate tamperings,
∆((nmExt(X, Y), (nmExt(fi(X), gi(Y)))_{i=1}^C), (Um, (nmExt(fi(X), gi(Y)))_{i=1}^C)) ⩽ 2^{−aδ,Cn}.
Every output character has binary matrix rank at most Rδ,Cn and explicit separated encodings of
length Oδ,C(n). No entropy assumption is imposed on tampered images. The input rate δ is arbitrary
and is fixed independently of C. A separately source-strong companion has the same asymptotic output
and error parameters." Printed p.79 (PDF p.81): the family "is specified at every positive length".

For an integer `C ≥ 1` and `0 < δ ≤ 1` there are `c, a, R > 0`, an encoding-length constant
`D' > 0`, polynomial-time machines `Fm` (`nmExt(x, y) = Fm [x, y]`), `Um`, `Vm` (the encodings
`u(x) = Um [x]`, `v(y) = Vm [y]`), constants `c', a' > 0` and a polynomial-time machine `Gm` such that
for every `n ≥ 1` there are `m ≥ cn`, `D ≤ D'n` and `m' ≥ c'n` with:
1. `nmExt` outputs exactly `m` bits and is a `C`-non-malleable two-source extractor at entropy `δn`
   with error `2^{−an}` (Definition 2.2: every admissible `C`-tuple, actual tampered outputs, no
   entropy assumption on tampered images);
2. every output character `(x, y) ↦ β · nmExt(x, y)` has `rank₂ ≤ Rn`;
3. `u, v` output exactly `D` bits and every output character is a bilinear form
   `u(x)ᵀ M_β v(y)` in these same two maps (common binary features, Definition 2.12);
4. the companion `Gm [x, y]` outputs exactly `m'` bits and is separately source strong
   (Definition 2.3) `C`-non-malleable at entropy `δn` with error `2^{−a'n}`.

**Formalization Note.** "Deterministic polynomial-time family" and "explicit" are one
`LowErrExt.IsPolyTime` machine each for all `n`, chosen after `C, δ` and the constants; inputs are
the bit strings (`List.ofFn`). "Explicit separated encodings of length `O_{δ,C}(n)`" is read as one
common pair of explicit encodings for all characters (the stronger reading; the construction's
trace-dual bases, p.73, give it). The companion's constants `c', a'` are its own ("the same
asymptotic parameters"). `k ≥ δn` sources are those with `H∞ ≥ δn`, arbitrary probability mass
functions. `{0,1}^m` is `Fin m → Bool` for the extractor property and `𝔽₂^m` (`machineVec`) for
characters. -/
theorem theorem_3_64 (C : ℕ) (hC : 1 ≤ C) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c a R : ℝ, 0 < c ∧ 0 < a ∧ 0 < R ∧ ∃ D' : ℝ, 0 < D' ∧
      ∃ Fm Um Vm : List (List Bool) → List Bool,
        IsPolyTime Fm ∧ IsPolyTime Um ∧ IsPolyTime Vm ∧
      ∃ c' a' : ℝ, 0 < c' ∧ 0 < a' ∧ ∃ Gm : List (List Bool) → List Bool, IsPolyTime Gm ∧
        ∀ n : ℕ, 1 ≤ n → ∃ m D m' : ℕ, c * n ≤ m ∧ (D : ℝ) ≤ D' * n ∧ c' * n ≤ m' ∧
          (∀ x y : Fin n → Bool, (Fm [List.ofFn x, List.ofFn y]).length = m) ∧
          IsNMExt C (δ * n) ((2 : ℝ) ^ (-(a * n)))
            (fun x y : Fin n → Bool => listOut m (Fm [List.ofFn x, List.ofFn y])) ∧
          (∀ β : Fin m → ZMod 2,
            (rank2 (fun x y : Fin n → Bool =>
              dotF2 β (machineVec Fm m [List.ofFn x, List.ofFn y])) : ℝ) ≤ R * n) ∧
          (∀ x : Fin n → Bool, (Um [List.ofFn x]).length = D) ∧
          (∀ y : Fin n → Bool, (Vm [List.ofFn y]).length = D) ∧
          (∀ β : Fin m → ZMod 2, ∃ M : Matrix (Fin D) (Fin D) (ZMod 2),
            ∀ x y : Fin n → Bool, dotF2 β (machineVec Fm m [List.ofFn x, List.ofFn y]) =
              dotProduct (machineVec Um D [List.ofFn x]) (M.mulVec (machineVec Vm D [List.ofFn y]))) ∧
          (∀ x y : Fin n → Bool, (Gm [List.ofFn x, List.ofFn y]).length = m') ∧
          IsSourceStrongNM C (δ * n) ((2 : ℝ) ^ (-(a' * n)))
            (fun x y : Fin n → Bool => listOut m' (Gm [List.ofFn x, List.ofFn y])) := by sorry

end OptTwoSrcExt.Supplement
