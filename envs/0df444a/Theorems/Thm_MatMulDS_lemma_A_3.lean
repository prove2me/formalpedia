-- Prove2me | Theorems.Thm_MatMulDS_lemma_A_3
-- name    : MatMulDS.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:02:37.806531+00:00
-- url     : https://prove2.me/theorems/05bcba05-6e85-416c-840c-5688c74a2471
-- title:
--   Lemma A.3 — a consistent labeling of a family of sets
-- statement:
--   Let $\tilde L\ge1$, let $U$ be a ground set and let $\mathcal F$ be a family of at most $e^{O(\tilde L)}$ subsets of $U$, each of size $s=e^{\Theta(\tilde L)}$. For all sufficiently large $\tilde L$ one can pick an integer
--   $$\tilde s=\Theta(s/\tilde L^2)$$
--   and, in $|\mathcal F|s^2\,\mathrm{poly}(\tilde L)$ time, construct $\chi:U\to[\tilde s]$ mapping each set of $\mathcal F$ onto $[\tilde s]$, and for every $S\in\mathcal F$, $i\in[\tilde s]$ a representative $\mathrm{rep}_S(i)\in S$ with $\chi(\mathrm{rep}_S(i))=i$.
--
--   This is what lets a shared right variable receive one consistent matrix entry across block sequences.
--
--   Differences from the source:
--   - encoding: "a family of sets" with time $|\mathcal F|s^2\mathrm{poly}(\tilde L)$ → $\mathcal F$ nonempty ($1\le m$); reason: for an empty family the bound is $0$ and a program takes a step; that case has nothing to label
--   - encoding: $e^{O(\tilde L)}$, $e^{\Theta(\tilde L)}$, "time" → constants $c_1,c_2,c_3$ before the rest; steps of one word program on the published RAM for every word size above a threshold logarithmic in the input numbers; reason: the meaning of the asymptotics; the source counts operations on such words
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.3, p.70 (PDF p.72)

import Mathlib
import Definitions.Def_MatMulDS_wordRun

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

/-- **Lemma A.3 (Consistent Labeling), p.70** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256
6c5a1c16…). Let `L̃ ≥ 1`, let `U` be a ground set, and let `𝓕` be a family of at most `e^{O(L̃)}` subsets of `U`, each of
size `s = e^{Θ(L̃)}`. For all sufficiently large `L̃` we can pick an integer `s̃ = Θ(s / L̃²)` such that in
`|𝓕| s² poly(L̃)` time we can construct `χ : U → [s̃]` mapping each set of `𝓕` surjectively onto `[s̃]`, and for every set
`S ∈ 𝓕` and `i ∈ [s̃]` a representative `rep_S(i)`, an element of `S` mapped to `i`.

**Formalization Note.**
* `c₁`, `c₂`, `c₃` are the implicit constants of `e^{O(L̃)}` and `e^{Θ(L̃)}`; the constants of the lemma come after them
  and before `L̃` and the family (trap 8). `poly(L̃)` is `(L̃ + 1)^c`.
* Time: steps of one fixed word program on the published RAM, for every word size above a threshold logarithmic in the
  input numbers. The input is `u, m, s, ⌈L̃⌉` and then the elements of the sets, each set in increasing order.
* Output: cell `0` holds `s̃`, and cells `1`, `2` point to the tables of `χ` and `rep`. The table of `χ` is indexed by the
  elements, and is `0` (the default of the memory) wherever the program did not write. So a large `U` costs no time.
* The family is nonempty: for `m = 0` the time bound would be `0`, and a program takes at least one step. -/
theorem lemma_A_3 (c₁ c₂ c₃ : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₂₃ : c₂ ≤ c₃) :
    ∃ (L₀ a₁ a₂ C : ℝ) (c K : ℕ) (Prog : List AInstr),
      0 < a₁ ∧ a₁ ≤ a₂ ∧ 0 < C ∧ IsWordProgram Prog ∧
      ∀ Lt : ℝ, 1 ≤ Lt → L₀ ≤ Lt →
      ∀ (u m s : ℕ) (Fam : Fin m → Finset (Fin u)),
        1 ≤ m → (m : ℝ) ≤ Real.exp (c₁ * Lt) →
        Real.exp (c₂ * Lt) ≤ s → (s : ℝ) ≤ Real.exp (c₃ * Lt) →
        (∀ i, (Fam i).card = s) →
        ∃ (st : ℕ) (χ : Fin u → Fin st) (rep : Fin m → Fin st → Fin u),
          a₁ * s / Lt ^ 2 ≤ st ∧ (st : ℝ) ≤ a₂ * s / Lt ^ 2 ∧
          (∀ i l, rep i l ∈ Fam i ∧ χ (rep i l) = l) ∧
          ∀ w : ℕ, K * Nat.clog 2 (u + m + s + ⌈Lt⌉₊ + 2) + K ≤ w →
            ∃ (t : ℕ) (mem : ℤ → BitVec w),
              wordRun Prog w
                ([(u : ℤ), (m : ℤ), (s : ℤ), (⌈Lt⌉₊ : ℤ)] ++
                  (List.finRange m).flatMap fun i =>
                    ((Fam i).sort (· ≤ ·)).map fun x => ((x : ℕ) : ℤ)) t = some mem ∧
              (t : ℝ) ≤ C * m * s ^ 2 * (Lt + 1) ^ c ∧
              (mem 0).toNat = st ∧
              (∀ x : Fin u, (mem ((mem 1).toInt + (x : ℕ))).toNat = χ x) ∧
              (∀ (i : Fin m) (l : Fin st),
                (mem ((mem 2).toInt + (i : ℕ) * st + (l : ℕ))).toNat = rep i l) := by sorry

end MatMulDS
