-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_5_3
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:28.512573+00:00
-- url     : https://prove2.me/theorems/ee9a6c8c-7abd-4170-9167-096c4422897c
-- title:
--   Lemma 5.3 — all tables in time ω^Λ·Λ^{O(1)}·O(n²)
-- statement:
--   There are a deterministic program and absolute constants such that, given any supplied structure $P$ of §4 on $n$ vertices, with $b\ge4$, $\theta<2M$ and $\gamma\in(0,1)$, the program computes all tables $F_C$, together with an allowed set attaining each finite entry of the root table, in time
--
--   $$\omega^\Lambda\cdot\Lambda^{O(1)}\cdot O(n^2),\qquad \omega=\lfloor 2/\gamma\rfloor+2,\quad \Lambda=\tau(b+1)(2/\sigma+1)^2 .$$
--
--   The tables are those of the supplied structure, which is encoded as input in the Proposition 4.10 layout. The output contains a fixed directory of absolute table addresses, all table entries, and the root witness bitmaps. Specializing to the good shift fixed at the opening of §5 gives the source statement.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: time in the word-RAM model with constant-time endpoint comparisons → step count of a program of the published Light language (each primitive operation costs one step, including loads, arithmetic, tests and control flow); reason: explicit charged program syntax with constants quantified before all data; comparing two raw endpoints costs a constant number of steps
--   - encoding: no explicit space bound → space limit S bounded by the same expression; depth limit T; reason: Light runs need finite limits; the source's proof gives this space (PDF p. 19, 21), and a run of T steps cannot nest more than T calls
--   - encoding: ω^Λ·Λ^{O(1)}·O(n²) → C·ω^Λ·Λ^c·(n + 1)² with C, c absolute; reason: the O's become absolute constants; (n+1)² as for Proposition 4.10
--   - reading: a parameter γ ∈ (0, 1) → γ = p/q with naturals 0 < p < q in the input; reason: a program receives a finite description of γ; every rational in (0, 1) is admitted, and the final proof uses γ = ε/16
--   - reading: words of Θ(log n) bits → word limit (n + q + b + 2)^c·ω^Λ·Λ^c; reason: read Θ(log n) with b and the finite description of γ fixed; the uniform bound also holds the input numbers and an address of the ω^Λ·Λ^{O(1)}·O(n log n) table memory used on PDF p. 21
--   - encoding: the structure of Proposition 4.10 fixed throughout §5 → a universally quantified Setup P supplied as n, b, p, q followed by structList P; vertices Fin n, cells heap indices and group ids least vertices; reason: the input supplies the source construction and every table and witness refers to that same P; no output structure is chosen existentially
--   - encoding: “computed” tables and witness sets → a fixed directory of absolute table base addresses, then tableList entries as (finite flag, value), then witness bitmaps; reason: the address of each entry is fixed by the returned base, heap order, mixed-radix index and table dimensions; only the attaining sets are existential
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 5.3, PDF p. 21 (printed p. 20)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 5.3, as a costed `Light` program: one program, with absolute constants, that for every
supplied structure `P` with `b ≥ 4`, every shift `θ < 2M`, and `γ = p/q ∈ (0, 1)` computes all
tables `F_C` of that same structure (layout `tableOutput`, including table addresses), together
with an allowed set attaining each finite entry of the root table, in
`ω^Λ · Λ^{O(1)} · O(n²)` steps, `ω = ⌊2/γ⌋ + 2`, `Λ = τ(b + 1)(2/σ + 1)²`.
Specializing to the good shift fixed in §5 gives the source statement. -/
theorem lemma_5_3 :
    ∃ (Prog : Light.Program) (C c : ℕ), ∀ (n : ℕ) (P : Setup n) (p q : ℕ),
      4 ≤ P.b → P.θ < 2 * bigM n → 0 < p → p < q →
        ∃ T S : ℕ,
          T ≤ C * omegaOf ((p : ℝ) / q) ^ bigLam P.b * bigLam P.b ^ c * (n + 1) ^ 2 ∧
          S ≤ C * omegaOf ((p : ℝ) / q) ^ bigLam P.b * bigLam P.b ^ c * (n + 1) ^ 2 ∧
          Light.Ends
            ⟨(((n + q + P.b + 2) ^ c * omegaOf ((p : ℝ) / q) ^ bigLam P.b * bigLam P.b ^ c : ℕ) : ℤ), S, T⟩
            Prog 0 entry (start (encodeTables P p q)) T
            (ReportsTables P ((p : ℝ) / q) S) := by sorry

end IntervalMaxCutEPTAS.Scheme
