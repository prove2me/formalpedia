-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_5_10
-- name    : OptTwoSrcExt.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:43:09.870877+00:00
-- url     : https://prove2.me/theorems/a04350f8-47c7-4209-bc05-7c1510a6cb3b
-- title:
--   Theorem 5.10 — advice generation from a two-sided strong seed
-- statement:
--   Let $F=\mathbb F_{2^q}$ with a fixed representation by $q$-bit strings, $h=\lceil n/q\rceil$, and $P_x$ the polynomial fingerprint of $x\in\{0,1\}^n$. Let $S=S(X,Y)\in F$ be a deterministic function of two independent sources $X,Y$ on $\{0,1\}^n$ and suppose
--   $$\Delta\big((S,X),(U_q,X)\big)\le\varepsilon_s,\qquad\Delta\big((S,Y),(U_q,Y)\big)\le\varepsilon_s,$$
--   with $U_q$ uniform on $F$ and independent of the retained source. Define the advice function
--   $$\mathrm{Adv}(x,y)=\big(S(x,y),P_x(S(x,y)),P_y(S(x,y))\big).\tag{5.3}$$
--   It has exactly $3q$ bits. For any $t$ split-state tamperings $(f_j,g_j)$ with $\Pr[(f_j(X),g_j(Y))=(X,Y)]=0$,
--   $$\Pr\big[\exists j:\mathrm{Adv}(X,Y)=\mathrm{Adv}(f_j(X),g_j(Y))\big]\le t\big(\varepsilon_s+(h-1)2^{-q}\big).\tag{5.4}$$
--   This applies to arbitrary tampering functions, with no entropy requirement on their outputs. Evaluation is polynomial time if $S$ is polynomial time.
--
--   **Formalization Note** The bound is stated for every field with $2^q$ elements and every bijective representation $\{0,1\}^q\to F$, so $\mathrm{Adv}$ takes values in $F^3$, written with exactly $3q$ bits. The polynomial-time clause is stated for families: for every polynomial-time field-construction machine and every polynomial-time machine computing $S$ on $[1^q,x,y]$ there is one polynomial-time machine that, at every $q$ where the field is constructed, outputs the $3q$ bits of $\mathrm{Adv}(x,y)$ in the power-basis representation.
--
--   Differences from the source:
--   - reading: "Evaluation is polynomial time if S is polynomial time" → for every polynomial-time field construction Pm and every polynomial-time Sm there is a polynomial-time Am with Am [1^q, x, y] = the 3q power-basis bits of Adv(x, y) whenever Pm constructs 𝔽_{2^q}; reason: polynomial time is a property of a family; q is passed in unary and the field is the explicit BinField
--   - encoding: a fixed representation of F = F_{2^q} → any field with 2^q elements and any bijection {0,1}^q ≃ F; reason: the bound is required for every choice
--   - encoding: two independent sources (no entropy assumption) → arbitrary probability mass functions X, Y on {0,1}ⁿ, law of the pair = indepPair; reason: published LowErrExt definition; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 5.10, p.107 (PDF p.109); fingerprints, §5.1.5, p.106 (PDF p.108)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_OptTwoSrcExt_Supplement_BinField
import Definitions.Def_OptTwoSrcExt_Supplement_IsNMExt
import Definitions.Def_OptTwoSrcExt_Supplement_fingerprint

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 5.10 (Advice generation from a two-sided strong seed).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 5.10, printed p.107 (PDF p.109): "Let
S = S(X, Y) ∈ F be a deterministic function of two independent sources and suppose
∆((S, X), (Uq, X)) ⩽ εs, ∆((S, Y), (Uq, Y)) ⩽ εs. Define a single deterministic advice function by
Adv(x, y) = (S(x, y), Px(S(x, y)), Py(S(x, y))). (5.3) It has exactly a = 3q bits. For any t
split-state tamperings (fj, gj) such that Pr[(fj(X), gj(Y)) = (X, Y)] = 0, its advice satisfies
Pr[∃j : Adv(X, Y) = Adv(fj(X), gj(Y))] ⩽ t(εs + (h − 1)2^{−q}). (5.4) This applies to arbitrary
tampering functions, with no entropy requirement on their outputs. Evaluation is polynomial time if
S is polynomial time." The setting (F = F_{2^q} with a fixed representation, h = ⌈n/q⌉, zero
padding, Px) is on printed p.106 (PDF p.108).

1. For all `q ≥ 1`, `n`, every field `F` with `2^q` elements and every representation
   `rep : {0,1}^q ≃ F`, every `S : {0,1}ⁿ × {0,1}ⁿ → F`, all independent sources `X, Y` on `{0,1}ⁿ`
   with `Δ((S, X), (U_q, X)) ≤ ε_s` and `Δ((S, Y), (U_q, Y)) ≤ ε_s` (`U_q` uniform on `F`,
   independent), and all `t` tamperings `(f_j, g_j)` with `Pr[(f_j(X), g_j(Y)) = (X, Y)] = 0`:
   `Pr[∃ j, Adv(X, Y) = Adv(f_j(X), g_j(Y))] ≤ t(ε_s + (h − 1)2^{−q})`, `h = ⌈n/q⌉`.
2. (Polynomial time.) For every polynomial-time field construction `Pm` and every polynomial-time
   machine `Sm` there is a polynomial-time machine `Am` such that, whenever `Pm` constructs
   `𝔽_{2^q}` (`q ≥ 1`), with `S(x, y)` the element written by `Sm [1^q, x, y]` and `rep` the
   power-basis representation, `Am [1^q, x, y]` is the `3q`-bit string of `Adv(x, y)`.

**Formalization Note.** `Adv` takes values in `F³`, which the representation writes with exactly
`3q` bits ("exactly a = 3q bits"). Sources are arbitrary probability mass functions; the bound in 1
holds for every choice of field and representation. In 2, "polynomial time" is
`LowErrExt.IsPolyTime` and field elements are written in the power basis of the explicit field
`BinField Pm q` (`eltBits`), `q` in unary. -/
theorem theorem_5_10 :
    (∀ (q n : ℕ), 1 ≤ q → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ q →
      ∀ (rep : (Fin q → Bool) ≃ F) (S : (Fin n → Bool) → (Fin n → Bool) → F)
        (X Y : PMF (Fin n → Bool)) (εs : ℝ),
        statDist ((indepPair X Y).map fun p => (S p.1 p.2, p.1))
            (indepPair (PMF.uniformOfFintype F) X) ≤ εs →
        statDist ((indepPair X Y).map fun p => (S p.1 p.2, p.2))
            (indepPair (PMF.uniformOfFintype F) Y) ≤ εs →
        ∀ (t : ℕ) (f g : Fin t → (Fin n → Bool) → (Fin n → Bool)),
          (∀ j, IsAdmissible X Y (f j) (g j)) →
          ((indepPair X Y).toOuterMeasure
              {p | ∃ j, advice rep S p.1 p.2 = advice rep S (f j p.1) (g j p.2)}).toReal ≤
            t * (εs + ((numBlocks n q : ℝ) - 1) * (2 : ℝ) ^ (-(q : ℝ)))) ∧
    (∀ Pm Sm : List (List Bool) → List Bool, IsPolyTime Pm → IsPolyTime Sm →
      ∃ Am : List (List Bool) → List Bool, IsPolyTime Am ∧
        ∀ q : ℕ, 1 ≤ q → IsFieldPolyAt Pm q → ∀ (n : ℕ) (x y : Fin n → Bool),
          let rep : (Fin q → Bool) → BinField Pm q :=
            fun v => eltOfVec Pm q fun i => if v i then 1 else 0
          let S : (Fin n → Bool) → (Fin n → Bool) → BinField Pm q :=
            fun x' y' => eltOfBits Pm q (Sm [List.replicate q true, List.ofFn x', List.ofFn y'])
          Am [List.replicate q true, List.ofFn x, List.ofFn y] =
            eltBits Pm q (advice rep S x y).1 ++ eltBits Pm q (advice rep S x y).2.1 ++
              eltBits Pm q (advice rep S x y).2.2) := by sorry

end OptTwoSrcExt.Supplement
