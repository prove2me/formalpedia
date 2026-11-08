-- Prove2me | Theorems.Thm_KelnerLinSolve_corollary_2_4
-- name    : KelnerLinSolve.corollary_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:53.014365+00:00
-- url     : https://prove2.me/theorems/fee939fa-ec03-46c6-8c8a-1d0994c30c7a
-- title:
--   Corollary 2.4 — coordinatewise reconstruction $\mathrm{Recover}(v,R,L,H)$ in $\tilde O(nL\log R)$
-- statement:
--   Assume the hypotheses of Theorem 2.1, with $n\ge1$ and each $v_i\in\{0,\dots,R^L-1\}$, and let $s$ be the bit length of $R^L$ (that is, $L\log_2R$ up to one bit). A multitape machine reading only $v_1\#\cdots\#v_n\#R\#L\#H$ (not $M$ or $b$) halts with the reduced coordinates $a_1\#d_1\#\cdots\#a_n\#d_n$ of $x^* = M^{-1}b$:
--
--   1. for every multiplication machine with a regular time bound $T$, some such machine runs within $C\,n\,T(s)\,\mathrm{lg}\,s$ steps, i.e. $O(n\,\mathsf M(L\log R)\log(L\log R))$;
--   2. unconditionally, some such machine runs within $C\,n\,s\,\mathrm{lg}(2+n+s)^K = \tilde O(nL\log R)$ steps, and for every constant $c$, on inputs with $L\le cn$, within $C'\,n^2\log R\cdot\mathrm{lg}(2+n+\log R)^{K'} = \tilde O(n^2\log R)$ steps.
--
--   This is the reconstruction cost used by the integer solver (Theorem 3.3).
--
--   Differences from the source:
--   - reading: M(s), the bit complexity of multiplying two s-bit integers → the time bound T of any multiplication machine (`IntMul.MultipliesAt`), assumed regular (T(s)/s nondecreasing, T(2s) ≤ 4T(s)), plus an unconditional Õ clause; reason: the page leaves M(s) unregulated; these are the standard conditions behind O(M(s) log s) (paper.md decision 6)
--   - reading: a function Recover(v, R, L, H) … in … bit operations → a multitape machine reading v₁#…#vₙ#R#L#H only, unconstrained on inputs outside the hypotheses; reason: the machine model of the goal (paper.md decision 2)
--   - encoding: L log R and log R → `Nat.size (R^L)` and `Nat.size R`; reason: bit lengths; they differ from L log₂ R and log₂ R by at most a factor 2 for R ≥ 2
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty vector, where no machine meets a zero bound
--   - encoding: the hypotheses of Theorem 2.1 → restated in full (det M ≠ 0, real T, naturals R, L, H); reason: as in the Theorem 2.1 item
--   - encoding: log(L log R) in the first bound → `IntMul.lg (Nat.size (R^L))`; reason: same up to a constant
--   - reading: Õ(nL log R) and Õ(n² log R) → C·n·s·lg(2+n+s)^K and C′·n²·`Nat.size R`·lg(2+n+`Nat.size R`)^K′; reason: §1.1: Õ suppresses factors polylogarithmic in the dimension and bit length
--   - encoding: if L = O(n) → for every c > 0, on inputs with L ≤ cn, with C′, K′ depending on c; reason: definition of O
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Corollary 2.4, p.7

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_MultitapeWords
import Definitions.Def_KelnerLinSolve_encInt
import Definitions.Def_KelnerLinSolve_SpaceWithin

open Matrix

namespace KelnerLinSolve

/-- **Corollary 2.4**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027
submission (sha256 d1af55cb…), p.7. "Under the hypotheses of Theorem 2.1, represent each `vᵢ` in
`{0, …, R^L − 1}`. There is a function `Recover(v, R, L, H)` that recovers the exact solution
`x* = M⁻¹b` by applying scalar rational reconstruction to each coordinate, in
`O(n M(L log R) log(L log R)) = Õ(nL log R)` bit operations. In particular, if `L = O(n)`, the
reconstruction cost is `Õ(n² log R)`."

Two conjuncts, one per form of the bound: (b) for every multiplication machine with a regular time
bound `T`, a machine within `C · n · T(s) · lg s` steps; (c) a machine within
`C · n · s · lg(2 + n + s)^K` steps (`Õ(nL log R)`) which, for every constant `c` and all inputs with
`L ≤ cn`, also runs within `C' · n² · log R · lg(2 + n + log R)^{K'}` steps (the "In particular"
clause). Here `s = Nat.size (R^L)`, the bit length of `R^L` (`L log₂ R` up to one bit), and
`log R` is `Nat.size R`.

**Formalization Note.** The machine reads only `v₁ # ⋯ # vₙ # R # L # H` in binary: `M` and `b`
are not on the tape. On every input meeting the hypotheses of Theorem 2.1 (with `vᵢ ∈ {0, …, R^L−1}`,
`n ≥ 1`) it halts with `a₁ # d₁ # ⋯ # aₙ # dₙ`, the reduced coordinates of `x* = M⁻¹b` over `ℚ`; on
other inputs it is unconstrained. `M(·)` is the bound `T` of a given multiplication machine
(`IntMul.MultipliesAt`), assumed regular (`IsRegularTimeBound`). -/
theorem corollary_2_4 :
    (∀ (Mul : IntMul.MultitapeTM) (T : ℕ → ℝ), (∀ s : ℕ, 1 ≤ s → IntMul.MultipliesAt Mul s (T s)) →
      IsRegularTimeBound T →
      ∃ (Rec : IntMul.MultitapeTM) (C : ℝ), 0 < C ∧
        ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (R L H : ℕ) (Tb : ℝ)
          (v : Fin n → ℕ), 1 ≤ n → M.det ≠ 0 → 2 ≤ R → 1 ≤ L → Int.gcd (R : ℤ) M.det = 1 →
          1 ≤ Tb → (∀ i j, |(M i j : ℝ)| ≤ Tb) → (∀ i, |(b i : ℝ)| ≤ Tb) →
          (n : ℝ) ^ ((n : ℝ) / 2) * Tb ^ n ≤ H →
          (∀ i, ((R : ℤ) ^ L) ∣ (M *ᵥ fun j => (v j : ℤ)) i - b i) → 2 * H ^ 2 < R ^ L →
          (∀ i, v i < R ^ L) →
          ∃ t : ℕ, (t : ℝ) ≤ C * n * T (Nat.size (R ^ L)) * (IntMul.lg (Nat.size (R ^ L)) : ℝ) ∧
            Rec.HaltsWithOutputW
              (IntMul.joinSep ((List.finRange n).map (fun i => encNat (v i))
                ++ [encNat R, encNat L, encNat H])) t
              (encRatVec ((M.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (b i : ℚ)))) ∧
    (∃ (Rec : IntMul.MultitapeTM) (C : ℝ) (K : ℕ), 0 < C ∧
      (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (R L H : ℕ) (Tb : ℝ)
          (v : Fin n → ℕ), 1 ≤ n → M.det ≠ 0 → 2 ≤ R → 1 ≤ L → Int.gcd (R : ℤ) M.det = 1 →
          1 ≤ Tb → (∀ i j, |(M i j : ℝ)| ≤ Tb) → (∀ i, |(b i : ℝ)| ≤ Tb) →
          (n : ℝ) ^ ((n : ℝ) / 2) * Tb ^ n ≤ H →
          (∀ i, ((R : ℤ) ^ L) ∣ (M *ᵥ fun j => (v j : ℤ)) i - b i) → 2 * H ^ 2 < R ^ L →
          (∀ i, v i < R ^ L) →
          ∃ t : ℕ, (t : ℝ) ≤ C * n * (Nat.size (R ^ L) : ℝ) * polylog K (2 + n + Nat.size (R ^ L)) ∧
            Rec.HaltsWithOutputW
              (IntMul.joinSep ((List.finRange n).map (fun i => encNat (v i))
                ++ [encNat R, encNat L, encNat H])) t
              (encRatVec ((M.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (b i : ℚ)))) ∧
      (∀ c : ℝ, 0 < c → ∃ (C' : ℝ) (K' : ℕ), 0 < C' ∧
        ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (R L H : ℕ) (Tb : ℝ)
          (v : Fin n → ℕ), 1 ≤ n → M.det ≠ 0 → 2 ≤ R → 1 ≤ L → Int.gcd (R : ℤ) M.det = 1 →
          1 ≤ Tb → (∀ i j, |(M i j : ℝ)| ≤ Tb) → (∀ i, |(b i : ℝ)| ≤ Tb) →
          (n : ℝ) ^ ((n : ℝ) / 2) * Tb ^ n ≤ H →
          (∀ i, ((R : ℤ) ^ L) ∣ (M *ᵥ fun j => (v j : ℤ)) i - b i) → 2 * H ^ 2 < R ^ L →
          (∀ i, v i < R ^ L) →
          (L : ℝ) ≤ c * n →
          ∃ t : ℕ, (t : ℝ) ≤ C' * (n : ℝ) ^ 2 * (Nat.size R : ℝ) * polylog K' (2 + n + Nat.size R) ∧
            Rec.HaltsWithOutputW
              (IntMul.joinSep ((List.finRange n).map (fun i => encNat (v i))
                ++ [encNat R, encNat L, encNat H])) t
              (encRatVec ((M.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (b i : ℚ))))) := by sorry

end KelnerLinSolve
