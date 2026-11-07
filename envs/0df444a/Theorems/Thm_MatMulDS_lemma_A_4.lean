-- Prove2me | Theorems.Thm_MatMulDS_lemma_A_4
-- name    : MatMulDS.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:08.232515+00:00
-- url     : https://prove2.me/theorems/641a6c07-edc2-455a-af96-35a4bcbd86ef
-- title:
--   Lemma A.4 — embedding matrix multiplication into $T_{\mathrm{big}}$
-- statement:
--   Let $L$ be admissible and sufficiently large, and let $\pi$ be a distribution on $O$ with rational values, uniform within each block, with $\mathrm{len}(\pi)>0$. There are integers $\widetilde{\mathrm{Mid}}(\pi),\widetilde{\mathrm{Col}}(\pi)$, labelings $\chi_{\mathrm{mid}},\chi_{\mathrm{col}}$ and representatives such that, with
--   $$N_0=\mathrm{Row}(\pi)K_{\mathrm{block}}(\pi)\widetilde{\mathrm{Col}}(\pi),\qquad D_0=\widetilde{\mathrm{Mid}}(\pi)^2:$$
--
--   1. for matrices $A,B$ of the tile and the assignment of variables of the lemma,
--   $$(AB)[(\boldsymbol\beta,i,c'),(c,\boldsymbol\beta',i')]=\text{the output of }T_{\mathrm{big}}\text{ at }z_{ij}\otimes z'_{j'i'},\quad j=\mathrm{colrep}_{\boldsymbol\beta}(c),\ j'=\mathrm{colrep}_{\boldsymbol\beta'}(c');$$
--   2. $N_0=e^{LH(\pi)}/\mathrm{poly}(L)$ and $D_0=e^{2L\mathrm{len}(\pi)}/\mathrm{poly}(L)$;
--   3. the labelings and representatives are computed in $P_{\mathrm{base}}^{2L}\mathrm{poly}(L)$ time.
--
--   This turns selected outputs of a tensor power into a large matrix product, the tile.
--
--   Differences from the source:
--   - reading: $N_0=e^{LH(\pi)}/\mathrm{poly}(L)$, and likewise $D_0$ → two-sided: $e^{LH(\pi)}(L+1)^{-c}\le N_0\le e^{LH(\pi)}$, and likewise $D_0$; reason: an equality with $/\mathrm{poly}(L)$ is two-sided; the upper bounds hold since $\widetilde{\mathrm{Col}}\le\mathrm{Col}$ and $\widetilde{\mathrm{Mid}}\le\mathrm{Mid}$
--   - encoding: "time" → steps of one word program on the published RAM, from the input $L$, for every word size at least $K'L+K'$, with tables in `HoldsTables`; reason: codes of strings have about $L$ bits; the source counts operations on such words
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.4, p.71 (PDF p.73)

import Mathlib
import Definitions.Def_MatMulDS_BlockSeq

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Lemma A.4 (Embedding Matrix Multiplication), p.71** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held
file sha256 6c5a1c16…). For every sufficiently large admissible `L`, there are `M̃id(π)`, `C̃ol(π)`, labelings `χmid`,
`χcol` and representatives `midrep_β`, `colrep_β` such that, with `N0 = Row(π) Kblock(π) C̃ol(π)` and `D0 = M̃id(π)²`:
* the setting of variables of the lemma gives (A.11): the entry `(AB)[(β, i, c′), (c, β′, i′)]` is the output of `T_big` at
  `z_ij ⊗ z′_j′i′`, with `j = colrep_β(c)` and `j′ = colrep_β′(c′)`;
* the matrix dimensions satisfy (A.12);
* the functions and representatives are computed in `P_base^{2L} poly(L)` time.

**Formalization Note.**
* (A.12) reads `N0 = e^{L H(π)} / poly(L)` and is two-sided: `e^{L H(π)} (L+1)^{−c} ≤ N0 ≤ e^{L H(π)}`, and likewise for `D0`.
* "Sufficiently large" is `L₀ ≤ L`, and the constants are fixed before `L`.
* The left and right assignments are functions of the variables of `T_big` alone (`tileLeft`, `tileRight`), since a shared
  right variable can receive only one value.
* Time: steps of one fixed word program, from the input `L`, for every word size at least `K L + K`: the strings have codes
  of about `L` bits. The tables are as in `HoldsTables`. -/
theorem lemma_A_4 (F : Type) [Field F] (T : BlockTensor I K J B) (D : IdentityData I K J P)
    (hD : D.Computes T) (π : I × J → ℚ) (hπ : IsBlockDistribution T π) (hlen : 0 < lenPi T π) :
    ∃ (L₀ c K' : ℕ) (C : ℝ) (Prog : List AInstr),
      0 < C ∧ IsWordProgram Prog ∧
      ∀ L : ℕ, L₀ ≤ L → IsAdmissible T π L →
      ∃ (m cc : ℕ) (χmid : (Fin L → K) → Fin m) (χcol : (Fin L → J) → Fin cc)
        (midrep : BlockSeq T π L → Fin m → (Fin L → K))
        (colrep : BlockSeq T π L → Fin cc → (Fin L → J)),
        (∀ s l, midrep s l ∈ midSet T s.1 ∧ χmid (midrep s l) = l) ∧
        (∀ s l, colrep s l ∈ colSet T s.1 ∧ χcol (colrep s l) = l) ∧
        Fintype.card (TileRow T π L cc) = rowCount T π L * Kblock T π L * cc ∧
        Fintype.card (TileCol T π L cc) = rowCount T π L * Kblock T π L * cc ∧
        -- (A.11)
        (∀ (A : Matrix (TileRow T π L cc) (Fin m × Fin m) F)
           (B' : Matrix (Fin m × Fin m) (TileCol T π L cc) F)
           (s : BlockSeq T π L) (i : {i : Fin L → I // i ∈ rowSet T s.1}) (c' : Fin cc)
           (c : Fin cc) (s' : BlockSeq T π L) (i' : {i : Fin L → I // i ∈ rowSet T s'.1}),
          (A * B') ⟨s, i, c'⟩ ⟨s', c, i'⟩ =
            bigOutput T s.1 s'.1 (tileLeft A χmid χcol midrep) (tileRight B' χmid χcol midrep)
              i.1 (colrep s c) (colrep s' c') i'.1) ∧
        -- (A.12)
        Real.exp (L * entropy T π) / ((L : ℝ) + 1) ^ c ≤ ((rowCount T π L * Kblock T π L * cc : ℕ) : ℝ) ∧
        ((rowCount T π L * Kblock T π L * cc : ℕ) : ℝ) ≤ Real.exp (L * entropy T π) ∧
        Real.exp (2 * L * lenPi T π) / ((L : ℝ) + 1) ^ c ≤ ((m ^ 2 : ℕ) : ℝ) ∧
        ((m ^ 2 : ℕ) : ℝ) ≤ Real.exp (2 * L * lenPi T π) ∧
        -- the time bound
        ∀ w : ℕ, K' * L + K' ≤ w →
          ∃ (t : ℕ) (mem : ℤ → BitVec w),
            wordRun Prog w [(L : ℤ)] t = some mem ∧
            (t : ℝ) ≤ C * (Fintype.card P : ℝ) ^ (2 * L) * ((L : ℝ) + 1) ^ c ∧
            HoldsTables mem χmid χcol midrep colrep := by sorry

end MatMulDS
