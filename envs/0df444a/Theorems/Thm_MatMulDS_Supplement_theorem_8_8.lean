-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_8
-- name    : MatMulDS.Supplement.theorem_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:19:35.871798+00:00
-- url     : https://prove2.me/theorems/b35cf2b7-5ba8-45b3-ba13-eaed6324c51a
-- title:
--   Theorem 8.8 — dynamic matrix inverse: $O(n^{3/2-\xi})$ updates, $O(n^{1/2-\xi'})$ queries, $n^{\omega+o(1)}$ initialization
-- statement:
--   Let $\beta$ be an admissible saving, set $\xi=\beta(1-2\beta)/2$ and $\xi'=\beta(1-\beta)/2$, and let $A\in\mathbb F^{n\times n}$ be a nonsingular matrix over a field $\mathbb F$ of characteristic zero that undergoes updates to its entries that keep it nonsingular. Then there is a deterministic exact data structure supporting
--
--   1. a change to one entry of $A$ in $O(n^{3/2-\xi})=O(n^{1.4998668})$ time;
--   2. a query for one entry of $A^{-1}$ in $O(n^{1/2-\xi'})=O(n^{0.4998668})$ time;
--   3. $n^{\omega+o(1)}$ initialization time.
--
--   All operation bounds are worst-case numbers of field operations. Over $\mathbb F_p$ for a prime $p\le n^{O(1)}$, the same holds on the word RAM with $\tilde O$ in place of $O$.
--
--   This beats both bounds of the Mv-hinted Mv conjecture of van den Brand, Nanongkai and Saranurak at $\tau=1/2$, refuting it, and underlies the dynamic graph results of Section 8.
--
--   Differences from the source:
--   - encoding: "worst-case numbers of field operations" → field operations counted by `fexec` on coin-free programs with a fixed list of constants of $\mathbb F$, every word size $w\ge K\lceil\log_2(n+1)\rceil+K$; reason: the source's cost measure on the mission's machine
--   - encoding: operations → set $A[i,j]:=x$ (words $0,i,j$, field element $x$) or query $A^{-1}[i,j]$ (words $1,i,j$, answer in field cell $-1$), on persistent memories (`DynOK`), for every sequence; an update making $A$ singular ends the guarantee; reason: a layout; "a change to one entry" sets it to a new value
--   - reading: $n^{\omega+o(1)}$ initialization → one program, and for every $\varepsilon>0$ a constant $C_\varepsilon$ with at most $C_\varepsilon n^{\omega+\varepsilon}$; update and query constants fixed before $\varepsilon$; $\omega=$ `omegaExp F 1 1 1`; reason: the stronger reading: one data structure with all three bounds
--   - encoding: over $\mathbb F_p$, $p\le n^{O(1)}$, word RAM, $\tilde O$ → for every $c$, word programs for all primes $p\le n^c$ (chosen after $c$), entries as representatives in $[0,p)$, $\tilde O=C(\log n+1)^{c'}$, $\omega$ of characteristic zero; reason: the meaning of $n^{O(1)}$ and $\tilde O$; the paper's $\omega$ is that of characteristic zero
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - encoding: the numerical form $O(n^{1.4998668})$, $O(n^{0.4998668})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.8, p.55 (PDF p.57)

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_DynOK

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.8, p.55** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, set `ξ = β(1 − 2β)/2` and `ξ′ = β(1 − β)/2`, and let `A ∈ F^{n×n}` be a nonsingular matrix over a field `F` of
characteristic zero that undergoes updates to its entries that keep it nonsingular. Then there is a deterministic exact data
structure supporting (a) a change to one entry of `A` in `O(n^{3/2−ξ}) = O(n^{1.4998668})` time; (b) a query for one entry of
`A^{−1}` in `O(n^{1/2−ξ′}) = O(n^{0.4998668})` time; (c) `n^{ω+o(1)}` initialization time. All operation bounds are worst-case
numbers of field operations. Over `F_p` for a prime `p ≤ n^{O(1)}`, the same holds on the word RAM with `Õ` in place of `O`.

**Formalization Note.**
* Over `F`: coin-free programs of the published machine, field operations counted (`FHalts`), with a fixed list of constants of `F`
  and every word size `w ≥ K⌈log₂(n+1)⌉ + K`. The initialization reads the words `n` and the field elements `cs`, then `A` in
  row-major order. An operation is `(i, j, some x)`, set `A[i, j] := x` (words `0, i, j`, field element `x`), or `(i, j, none)`,
  query `A^{−1}[i, j]` (words `1, i, j`; the answer in field cell `−1`), written to the negative cells (`withOp`); the memories
  persist between operations (`DynOK`), for every sequence of operations; an update that makes `A` singular ends the guarantee.
* `n^{ω+o(1)}`: one program, and for every `ε > 0` a constant `C_ε` with initialization within `C_ε n^{ω+ε}`; `ω` is the published
  `omegaExp F 1 1 1`. The update and query constants are fixed before `ε`.
* Over `F_p`: word programs (all steps counted), for every `c` and every prime `p ≤ n^c`, the program and constants chosen after `c`;
  input words `n, p`, then the entries of `A` as their representatives in `[0, p)`; update words `0, i, j, x`, query words `1, i, j`,
  the answer in word cell `−1`. `Õ` is `C (log n + 1)^{c'}`, and `ω` is `omegaExp ℚ 1 1 1`, that of characteristic zero.
* The numerical forms are the instance `β = 0.0002666`, stated as the last conjunct. -/
theorem theorem_8_8 (β : ℝ) (hβ : AdmissibleSaving β) :
    -- over a field of characteristic zero, counting field operations
    (∀ (F : Type) [Field F] [CharZero F] [DecidableEq F],
      ∃ (Pinit Pop : List AInstr) (cs : List F) (K : ℕ) (C : ℝ), 0 < C ∧
        (∀ i ∈ Pinit, ¬ i.IsCoin) ∧ (∀ i ∈ Pop, ¬ i.IsCoin) ∧
        ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
          ∀ (n : ℕ), 1 ≤ n → ∀ A : Matrix (Fin n) (Fin n) F, IsUnit A.det →
          ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          ∃ m₀ : (ℤ → BitVec w) × (ℤ → F),
            FHalts Pinit (aloadWords w [(n : ℤ)], aloadFields (cs ++ matList A))
              ⌈Cε * (n : ℝ) ^ (omegaExp F 1 1 1 + ε)⌉₊ m₀ ∧
            ∀ ops : List (Fin n × Fin n × Option F),
              DynOK (S := Matrix (Fin n) (Fin n) F)
                (fun m op t m' => FHalts Pop
                  (withOp m (match op.2.2 with
                    | some _ => [0, ((op.1 : ℕ) : ℤ), ((op.2.1 : ℕ) : ℤ)]
                    | none => [1, ((op.1 : ℕ) : ℤ), ((op.2.1 : ℕ) : ℤ)])
                    (match op.2.2 with | some x => [x] | none => [])) t m')
                (fun A op => match op.2.2 with
                  | some x => IsUnit (Matrix.of fun a b => if a = op.1 ∧ b = op.2.1 then x else A a b).det
                  | none => True)
                (fun A op => match op.2.2 with
                  | some x => Matrix.of fun a b => if a = op.1 ∧ b = op.2.1 then x else A a b
                  | none => A)
                (fun A op m' => match op.2.2 with
                  | some _ => True
                  | none => m'.2 (-1) = A⁻¹ op.1 op.2.1)
                (fun _ op _ => match op.2.2 with
                  | some _ => C * (n : ℝ) ^ ((3 : ℝ) / 2 - β * (1 - 2 * β) / 2)
                  | none => C * (n : ℝ) ^ ((1 : ℝ) / 2 - β * (1 - β) / 2))
                A m₀ ops) ∧
    -- over F_p on the word RAM
    (∀ c : ℕ, ∃ (Pinit Pop : List AInstr) (K c' : ℕ) (C : ℝ), 0 < C ∧
        IsWordProgram Pinit ∧ IsWordProgram Pop ∧
        ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
          ∀ (n p : ℕ), 1 ≤ n → p.Prime → p ≤ n ^ c → ∀ A : Matrix (Fin n) (Fin n) (ZMod p), IsUnit A.det →
          ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
          ∃ m₀ : (ℤ → BitVec w) × (ℤ → ℚ),
            aexec Pinit (fun _ => 0) ⌈Cε * (n : ℝ) ^ (omegaExp ℚ 1 1 1 + ε)⌉₊ 0 0
              (aloadWords w ([(n : ℤ), (p : ℤ)] ++ (entries A).map fun x => ((x.val : ℕ) : ℤ))) (aloadFields []) =
                some m₀ ∧
            ∀ ops : List (Fin n × Fin n × Option (ZMod p)),
              DynOK (S := Matrix (Fin n) (Fin n) (ZMod p))
                (fun m op t m' =>
                  let m₁ := withOp m (match op.2.2 with
                    | some x => [0, ((op.1 : ℕ) : ℤ), ((op.2.1 : ℕ) : ℤ), ((x.val : ℕ) : ℤ)]
                    | none => [1, ((op.1 : ℕ) : ℤ), ((op.2.1 : ℕ) : ℤ)]) []
                  aexec Pop (fun _ => 0) t 0 0 m₁.1 m₁.2 = some m')
                (fun A op => match op.2.2 with
                  | some x => IsUnit (Matrix.of fun a b => if a = op.1 ∧ b = op.2.1 then x else A a b).det
                  | none => True)
                (fun A op => match op.2.2 with
                  | some x => Matrix.of fun a b => if a = op.1 ∧ b = op.2.1 then x else A a b
                  | none => A)
                (fun A op m' => match op.2.2 with
                  | some _ => True
                  | none => (m'.1 (-1)).toInt = (((A⁻¹ op.1 op.2.1).val : ℕ) : ℤ))
                (fun _ op _ => match op.2.2 with
                  | some _ => C * (Real.log n + 1) ^ c' * (n : ℝ) ^ ((3 : ℝ) / 2 - β * (1 - 2 * β) / 2)
                  | none => C * (Real.log n + 1) ^ c' * (n : ℝ) ^ ((1 : ℝ) / 2 - β * (1 - β) / 2))
                A m₀ ops) ∧
    (3 : ℝ) / 2 - 0.0002666 * (1 - 2 * 0.0002666) / 2 ≤ 1.4998668 ∧
    (1 : ℝ) / 2 - 0.0002666 * (1 - 0.0002666) / 2 ≤ 0.4998668 := by sorry

end MatMulDS.Supplement
