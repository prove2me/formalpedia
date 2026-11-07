-- Prove2me | Theorems.Thm_MatMulDS_lemma_A_6
-- name    : MatMulDS.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:27.827838+00:00
-- url     : https://prove2.me/theorems/5b196e7d-2940-4703-99c3-6d9bc10fefe4
-- title:
--   Lemma A.6 — counting stored values and query terms (corrected: rational weights for time, $1+e^{2Lf}$)
-- statement:
--   Fix the data of Lemma A.5 and $\theta\ge0$, with $f,\xi$ as in (A.18). For all sufficiently large admissible $L$:
--
--   1. $|K_{\mathrm{key}}|\le(2L+1)e^{2Lf}$, and $K_{\mathrm{key}}$ and all stored values can be computed in $e^{2Lf}\,\mathrm{poly}(L)$ time;
--   2. for every selected output $o$, the right-hand side of (A.17) has at most $e^{2L\xi}\,\mathrm{poly}(L)$ terms, and these terms can be found in the same time.
--
--   These counts give the preprocessing and query costs of the data structure.
--
--   Differences from the source:
--   - correction: time $e^{2Lf}\mathrm{poly}(L)$ for $K_{\mathrm{key}}$ and stored values → time $(1+e^{2Lf})\mathrm{poly}(L)$; reason: false as printed: the five-term identity with weights $\mathrm{wt}+1$, $\pi$ uniform, $\eta_{\mathrm{pre}}=0$, $\theta=2$ satisfies every assumption, no string is light, and $e^{2Lf}\to0$, while a program takes a step; nothing changes when $f\ge0$
--   - correction: time claims for real weights and thresholds → the two time clauses take $\mathrm{wt}$ and $\eta_{\mathrm{pre}}$ rational; the two counts hold for all reals; reason: false on the machine for real data: for the five-term identity with $\pi$ uniform and an uncomputable $\eta_{\mathrm{pre}}\in(0,1/5)$, the light strings determine $\lfloor2L\eta_{\mathrm{pre}}\rfloor$ for all $L$, so no fixed finite program outputs them; the source only uses exact decimals
--   - encoding: "time", stored values, terms → steps of one program on the published RAM for word size at least $K'L+K'$, with field cell `encStr κ` holding the value at $\kappa$ and listed outputs; reason: the source counts operations on such words
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma A.6, p.76 (PDF p.78)

import Mathlib
import Definitions.Def_MatMulDS_Kkey
import Definitions.Def_MatMulDS_wordRun

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Lemma A.6 (Counting Stored Values and Query Terms), p.76** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file
sha256 6c5a1c16…), for every sufficiently large admissible `L` (Appendix A.3, p.74).
(i) `|Kkey| ≤ (2L + 1) e^{2Lf}`, and the set `Kkey` and all stored values can be computed in `e^{2Lf} poly(L)` time.
(ii) For every selected output `o`, the right-hand side of (A.17) has at most `e^{2Lξ} poly(L)` terms, and these terms can be found in
the same time.

**Formalization Note.**
* Time is the steps of one fixed program on the published RAM, for every word size at least `K L + K`. A finite program cannot read the
  bits of an arbitrary real threshold: with weights `0` and `1`, the set of light strings encodes `⌊2Lη⌋` for all `L`. So the two time
  clauses take `wt` and `η` rational, while the two counts hold for all real weights.
* The input of (i) is `L`, with the value `v κ` of the product at `κ` in field cell `encStr κ`. Its output is the list of keys in word
  cells `0` (the length), `1, 2, …`, with the stored values `val(κ, k)` in the field cells from `P_base^{2L}` on.
* The time in (i) is `(1 + e^{2Lf}) poly(L)`: when no string is light, `e^{2Lf}` can tend to `0`, and a program takes at least one step.
* The input of (ii) is `L` and the code of `o`. Its output is the list of the products of the first sum of (A.17), then the list of the
  keys of the boxes. -/
theorem lemma_A_6 (F : Type) [Field F] [DecidableEq F] (T : BlockTensor I K J B)
    (D : IdentityData I K J P) (hD : D.Computes T) (ρ : T.Out → P) (hρ : D.IsPrivateMap T ρ)
    (wt : P → ℝ) (hwt : D.IsCompatible T ρ wt) (π : I × J → ℚ) (hπ : IsBlockDistribution T π)
    (hlen : 0 < lenPi T π) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ mu π ρ wt) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ (L₀ c K' : ℕ) (C : ℝ), 0 < C ∧
      -- the two counts
      (∀ L : ℕ, L₀ ≤ L → IsAdmissible T π L →
        ((Kkey ρ wt η L).card : ℝ) ≤ (2 * L + 1) * Real.exp (2 * L * fRate wt θ η) ∧
        ∀ o : Fin (2 * L) → T.Out, IsSelected π L o →
          (((heavyRelevant π D ρ wt η o).card + (boxesOf D π ρ wt η o).card : ℕ) : ℝ) ≤
            C * Real.exp (2 * L * xiRate D π ρ wt η) * ((L : ℝ) + 1) ^ c) ∧
      -- the two time bounds, for rational weights and threshold
      ((∀ p, ∃ q : ℚ, wt p = q) → (∃ q : ℚ, η = q) →
        ∃ (Prog₁ Prog₂ : List AInstr),
          (∀ i ∈ Prog₁, ¬ i.IsCoin) ∧ IsWordProgram Prog₂ ∧
          (∀ L : ℕ, L₀ ≤ L → IsAdmissible T π L →
            ∀ (v : Str P L → F) (fm : ℤ → F), (∀ κ : Str P L, fm (encStr κ) = v κ) →
            ∀ w : ℕ, K' * L + K' ≤ w →
              ∃ (t : ℕ) (st : (ℤ → BitVec w) × (ℤ → F)) (keys : List (Str P L × ℕ)),
                aexec Prog₁ (fun _ => 0) t 0 0 (aloadWords w [(L : ℤ)]) fm = some st ∧
                (t : ℝ) ≤ C * (1 + Real.exp (2 * L * fRate wt θ η)) * ((L : ℝ) + 1) ^ c ∧
                keys.Nodup ∧ keys.toFinset = Kkey ρ wt η L ∧
                (st.1 0).toNat = keys.length ∧
                ∀ (i : ℕ) (hi : i < keys.length),
                  (st.1 (1 + 2 * i)).toNat = encStr keys[i].1 ∧
                  (st.1 (2 + 2 * i)).toNat = keys[i].2 ∧
                  st.2 (((Fintype.card P ^ (2 * L) + i : ℕ) : ℤ)) =
                    ∑ q ∈ keyBox D ρ keys[i].1 keys[i].2, v q) ∧
          (∀ L : ℕ, L₀ ≤ L → IsAdmissible T π L →
            ∀ o : Fin (2 * L) → T.Out, IsSelected π L o →
            ∀ w : ℕ, K' * L + K' ≤ w →
              ∃ (t : ℕ) (mem : ℤ → BitVec w) (prods : List (Str P L)) (boxes : List (Str P L × ℕ)),
                wordRun Prog₂ w [(L : ℤ), (encStr o : ℤ)] t = some mem ∧
                (t : ℝ) ≤ C * Real.exp (2 * L * xiRate D π ρ wt η) * ((L : ℝ) + 1) ^ c ∧
                prods.Nodup ∧ prods.toFinset = heavyRelevant π D ρ wt η o ∧
                boxes.Nodup ∧ (boxes.map fun x => keyBox D ρ x.1 x.2).toFinset = boxesOf D π ρ wt η o ∧
                (∀ x ∈ boxes, x ∈ Kkey ρ wt η L) ∧
                (mem 0).toNat = prods.length ∧ (mem 1).toNat = boxes.length ∧
                (∀ (i : ℕ) (hi : i < prods.length), (mem (2 + i)).toNat = encStr prods[i]) ∧
                ∀ (i : ℕ) (hi : i < boxes.length),
                  (mem (2 + prods.length + 2 * i)).toNat = encStr boxes[i].1 ∧
                  (mem (3 + prods.length + 2 * i)).toNat = boxes[i].2)) := by sorry

end MatMulDS
