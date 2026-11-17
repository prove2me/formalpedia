-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_6_11
-- name    : KAQROM.Supplement.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:55:09.315799+00:00
-- url     : https://prove2.me/theorems/6c8bbeae-f0c5-46e5-8ee1-f30cc3bd3004
-- title:
--   Theorem 6.11 — constant-round attack with quantum Bob: a passive classical attacker with $\sum_i(N^-_i+N^+_i)$ queries and $\mathrm{Adv}^{\mathrm{KR}}\ge\alpha-2\Delta_r$
-- statement:
--   Let $\Pi^{qb}$ be an alternating protocol $B_1,A_1,\dots,A_r,B_{r+1}$ with $r\ge1$ Alice stages (Definition 6.10). Alice's stage $A_i$ makes at most $a_i$ classical queries and Bob's stage $B_i$ at most $b_i$ quantum queries, $Q\ge\max\{1,\sum_{i=1}^r a_i+\sum_{i=1}^{r+1}b_i\}$ is a fixed integer, and $\alpha=\alpha_{\Pi^{qb}}$. For $\eta,\beta_i,\gamma_i\in(0,1)$ set (display (14))
--   $$
--   N^-_i=\Bigl\lceil\frac{Q}{\eta\beta_i}\Bigr\rceil,\quad N^+_i=\Bigl\lceil\frac{Q}{\eta\gamma_i}\Bigr\rceil\quad(1\le i\le r),\qquad N^-_{r+1}=0,
--   $$
--   and (display (15))
--   $$
--   \Delta_r=2r\eta+\sum_{i=1}^r\Bigl(2(a_i+N^+_i)\sqrt{\beta_i}+2b_{i+1}\sqrt{\gamma_i}+N^-_{i+1}\gamma_i\Bigr).
--   $$
--   Then there is a computationally unbounded passive classical attacker $E$ that receives the complete transcript after the honest run, makes at most $\sum_{i=1}^r(N^-_i+N^+_i)$ classical oracle queries, and computes its key guess from the answers without further queries, with
--   $$
--   \mathrm{Adv}^{\mathrm{KR}}_{\Pi^{qb},E}\ \ge\ \alpha-2\Delta_r .
--   $$
--   For a protocol with completeness error $\epsilon_c$ the advantage is at least $1-\epsilon_c-2\Delta_r$.
--
--   This extends Theorem 6.2 to any fixed number of rounds. It underlies the impossibility results for constant-round protocols, among them Theorem 7.5.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: keys in K ∪ {⊥} → Option K with ⊥ = none; reason: Lean convention; same instances
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - reading: a passive classical attacker that obtains its oracle information through learners and computes K∗ deterministically from their recorded view → a deterministic classical-query algorithm on the transcript (DetAttacker) with a worst-case query bound on every oracle and transcript; reason: this is the theorem's own description of the attacker; a deterministic attacker is in particular a randomized classical one
--   - encoding: completeness error ϵc(λ) → every real ϵc with 1 − ϵc ≤ α; reason: the definition of completeness error, at fixed λ
--   - encoding: indices i = 1, …, r and N⁻_{r+1} = 0 → 0-based i : Fin r (paper's i+1); Nm j = N⁻_{j+1} for j < r and Nm r = 0; P.b i.succ = b_{i+2}; reason: Lean indexing; summand i is the paper's summand i+1
--   - encoding: fix r ≥ 1 independently of λ → any r ≥ 1 (P.one_le_r) at the fixed λ; reason: at fixed λ independence of λ is vacuous
--   - encoding: a_i bound the queries of A_i → parameters a with the hypothesis AQueriesLe a; reason: the a_i are any worst-case bounds
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 6.11 with displays (14) and (15), p.63; Definition 6.10, pp.62–63

import Mathlib
import Definitions.Def_KAQROM_Supplement_DetAttacker
import Definitions.Def_KAQROM_Supplement_Alternating

namespace KAQROM.Supplement

open KAQROM

/-- **Theorem 6.11 (Constant-round attack with quantum Bob).** Let `Π^{qb}` be a protocol of
Definition 6.10 with `r ≥ 1` Alice stages, `a_i` bounding the queries of `A_i`, `b_i` those of
`B_i`, and `Q ≥ max{1, ∑ a_i + ∑ b_i}` a fixed integer. For `η, β_i, γ_i ∈ (0,1)` set
`N⁻_i := ⌈Q/(ηβ_i)⌉`, `N⁺_i := ⌈Q/(ηγ_i)⌉` (`1 ≤ i ≤ r`), `N⁻_{r+1} := 0` (display (14)). There
is a computationally unbounded passive classical attacker `E` making at most
`∑_{i=1}^r (N⁻_i + N⁺_i)` classical oracle queries with `Adv^{KR}_{Π^{qb},E} ≥ α − 2∆_r`, where
`∆_r := 2rη + ∑_{i=1}^r (2(a_i + N⁺_i)√β_i + 2b_{i+1}√γ_i + N⁻_{i+1}γ_i)` (display (15)); it
computes its key guess from its recorded view without further queries. For a protocol with
completeness error `ϵ_c`, the advantage is at least `1 − ϵ_c − 2∆_r`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 6.11 with
displays (14) and (15), p.63.

**Formalization Note.** Indices are 0-based: `i : Fin r` is the paper's `i + 1`; `β i`, `γ i`,
`a i`, `Np i` are `β_{i+1}`, `γ_{i+1}`, `a_{i+1}`, `N⁺_{i+1}`; `Nm j` is `N⁻_{j+1}` for `j < r` and
`0` for `j = r` (the paper's `N⁻_{r+1}`); `P.b i.succ` is `b_{i+2}`, so the summand at `i` is the
paper's summand at `i + 1`. The security parameter is fixed, so `r` is any integer `≥ 1`. The
attacker is a deterministic classical-query algorithm on `M_full` whose query bound holds on every
oracle and every transcript. -/
theorem theorem_6_11 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Alternating X ℓ Msg K) (a : Fin P.r → ℕ)
    (ha : P.AQueriesLe a) (Q : ℕ) (hQ : max 1 (∑ i, a i + ∑ j, P.b j) ≤ Q) (η : ℝ)
    (β γ : Fin P.r → ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hβ0 : ∀ i, 0 < β i) (hβ1 : ∀ i, β i < 1)
    (hγ0 : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i < 1) :
    let Nm : ℕ → ℕ := fun j => if h : j < P.r then ⌈(Q : ℝ) / (η * β ⟨j, h⟩)⌉₊ else 0
    let Np : Fin P.r → ℕ := fun i => ⌈(Q : ℝ) / (η * γ i)⌉₊
    let Δr : ℝ := 2 * P.r * η + ∑ i : Fin P.r,
      (2 * ((a i : ℝ) + Np i) * Real.sqrt (β i) + 2 * (P.b i.succ : ℝ) * Real.sqrt (γ i) +
        (Nm (i.val + 1) : ℝ) * γ i)
    ∃ E : DetAttacker (Fin (2 * P.r + 1) → Msg) X ℓ (Option K),
      E.QueriesLe (∑ i : Fin P.r, (Nm i.val + Np i)) ∧
      P.alpha - 2 * Δr ≤ P.advKR E ∧
      ∀ ϵc : ℝ, 1 - ϵc ≤ P.alpha → 1 - ϵc - 2 * Δr ≤ P.advKR E := by sorry

end KAQROM.Supplement
