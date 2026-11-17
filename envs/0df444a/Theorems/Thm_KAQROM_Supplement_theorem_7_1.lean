-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_7_1
-- name    : KAQROM.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:55:51.947079+00:00
-- url     : https://prove2.me/theorems/e63f32fc-301d-4860-8d9d-f477b40894ec
-- title:
--   Theorem 7.1 — attack on QPKE with classical-query key generation: advantage $\ge\alpha_\Sigma-\tfrac12-\delta-2(2q_{\mathrm{Enc}}+q_{\mathrm{Dec}})\sqrt\delta$
-- statement:
--   Let $\Sigma=(\mathrm{Gen},\mathrm{Enc},\mathrm{Dec})$ be a QPKE scheme with classical keys and classical-query key generation (Definition 3.12). Key generation makes at most $q_{\mathrm{Gen}}$ classical queries, encryption and decryption make at most $q_{\mathrm{Enc}}$ and $q_{\mathrm{Dec}}$ quantum queries, and $\alpha_\Sigma$ is the minimum correct-decryption probability.
--
--   1. For every $0<\delta<1$ there is a computationally unbounded quantum IND-CPA attacker $D_\delta$ with at most $\lceil q_{\mathrm{Gen}}/\delta^2\rceil+q_{\mathrm{Dec}}$ random-oracle queries and
--   $$
--   \mathrm{Adv}^{\mathrm{IND\text{-}CPA}}_{\Sigma,D_\delta}\ \ge\ \alpha_\Sigma-\tfrac12-\delta-2(2q_{\mathrm{Enc}}+q_{\mathrm{Dec}})\sqrt\delta .
--   $$
--   2. If $\alpha_\Sigma>0$, let $Q_\Sigma=\max\{1,2q_{\mathrm{Enc}}+q_{\mathrm{Dec}}\}$ and $\delta=(\alpha_\Sigma/(8Q_\Sigma))^2$. Then $D_\delta$ makes at most $\lceil 4096\,q_{\mathrm{Gen}}Q_\Sigma^4/\alpha_\Sigma^4\rceil+q_{\mathrm{Dec}}$ queries and $\mathrm{Adv}^{\mathrm{IND\text{-}CPA}}_{\Sigma,D_\delta}\ge\frac{47}{64}\alpha_\Sigma-\frac12$.
--   3. Consider a family of such schemes with negligible correctness error $\epsilon_c$ ($\alpha_\Sigma\ge1-\epsilon_c$), honest query bounds $q_{\mathrm{Gen}},q_{\mathrm{Enc}},q_{\mathrm{Dec}}$ bounded by polynomials in $\lambda$, and message length $\mu$ bounded by a polynomial. Then for every polynomial $p$ there is an attacker family with polynomially many queries and advantage at least $1/2-1/p(\lambda)-\nu(\lambda)$ for a negligible $\nu$. In particular the scheme is not query-bounded IND-CPA secure.
--   4. If key generation and decryption are classical algorithms and the ciphertext is classical, items 1–3 hold with a classical attacker, which makes only classical queries.
--
--   Encryption, decryption and the ciphertext may all be quantum in items 1–3.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - encoding: poly(λ), negl(λ), 'for every polynomial p' → λ-indexed families; the published PolyBounded and Negligible; p : Polynomial ℕ with positive values; reason: standard asymptotic notions; a positive polynomial is bounded by some (λ+2)^c
--   - reading: item 2: the attacker D_δ at δ = (α_Σ/(8Q_Σ))² → one attacker satisfying both the item-1 bounds at that δ and the 47/64 bounds; reason: it is the item-1 attacker at that δ
--   - encoding: a quantum attacker's number of queries → q0 + q1, the query rounds of its two stages; reason: classical queries are special quantum queries
--   - encoding: D1^H(Z_D, C) → D1 chosen by the classical data (pk, m0, m1) as well; reason: D0 can keep this classical data in Z_D; every D1 not depending on it is an instance
--   - encoding: 'not query-bounded IND-CPA secure' → the negation of 'every attacker family with polynomially bounded queries has negligible advantage'; reason: Definition 3.14's security notion for λ-indexed families
--   - encoding: key generation and decryption are classical algorithms and the ciphertext is classical; a classical attacker → the scheme type QPKE1c (Gen and Dec classical-query stages on a one-dimensional register, Enc quantum with classical output) and CINDAttacker (finitely many coin values); reason: a classical randomized algorithm with classical queries is exactly such a stage; finitely many coins make the existence claim stronger
--   - reading: 'the attacker can also be classical, with the same bounds' → items 1, 2 and 3 for the classical scheme type with classical attackers; reason: the stronger reading includes the asymptotic item
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.1, pp.71–72; Definitions 3.12 and 3.14, p.23

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_KAQROM_Supplement_CINDAttacker
import Definitions.Def_KAQROM_Supplement_QPKE1

namespace KAQROM.Supplement

open KAQROM
open PPADSIS.SubexpSIS

/-- **Theorem 7.1 (Attack on QPKE with classical-query key generation).** Let `Σ` be a QPKE scheme
with classical keys and classical-query key generation, as in Definition 3.12.

1. For every `0 < δ < 1` there is a computationally unbounded quantum IND-CPA attacker `D_δ`
   making at most `⌈q_Gen/δ²⌉ + q_Dec` random-oracle queries with
   `Adv^{IND-CPA}_{Σ,D_δ} ≥ α_Σ − 1/2 − δ − 2(2q_Enc + q_Dec)√δ`.
2. If `α_Σ > 0`, with `Q_Σ := max{1, 2q_Enc + q_Dec}` and `δ := (α_Σ/(8Q_Σ))²`,
   `Adv ≥ (47/64)α_Σ − 1/2` and `D_δ` makes at most `⌈4096 q_Gen Q_Σ⁴/α_Σ⁴⌉ + q_Dec` queries.
3. Consequently a scheme with negligible correctness error and honest query complexity bounded by
   `poly(λ)` is not query-bounded IND-CPA secure: for every polynomial `p`, an attacker making at
   most `poly(λ)` queries achieves advantage at least `1/2 − 1/p(λ) − negl(λ)`, for every
   message-length function `μ` bounded by a polynomial.
4. If key generation and decryption are classical algorithms and the ciphertext is classical,
   the attacker can also be classical, with the same bounds.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.1,
pp.71–72.

**Formalization Note.** The statement has four conjuncts: clauses 1–2 for one scheme (the attacker
of clause 2 is the clause-1 attacker at the stated `δ`, so it satisfies both bounds); clause 3 for
families indexed by `λ` (the published `Negligible` and `PolyBounded`; a polynomial `p` is a
`Polynomial ℕ` with positive values; "not query-bounded IND-CPA secure" is the negation of "every
attacker family with polynomially bounded queries has negligible advantage"); clause 4 repeats
clauses 1–3 for the schemes `QPKE1c` (classical `Gen`, `Dec`, ciphertext) with classical attackers
`CINDAttacker`. `q_Gen` (and `q_Dec` in clause 4) are any worst-case bounds; a quantum attacker's
query count is `q0 + q1`. -/
theorem theorem_7_1 :
    (∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ} (S : QPKE1 X ℓ μ) (qGen : ℕ),
      S.GenQueriesLe qGen →
      (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ D : INDAttacker S,
        D.q0 + D.q1 ≤ ⌈(qGen : ℝ) / δ ^ 2⌉₊ + S.qDec ∧
        S.alpha - 1 / 2 - δ - 2 * (2 * (S.qEnc : ℝ) + S.qDec) * Real.sqrt δ ≤ S.adv D) ∧
      (0 < S.alpha →
        let Qsig : ℕ := max 1 (2 * S.qEnc + S.qDec)
        let δ : ℝ := (S.alpha / (8 * Qsig)) ^ 2
        ∃ D : INDAttacker S,
          D.q0 + D.q1 ≤ ⌈(qGen : ℝ) / δ ^ 2⌉₊ + S.qDec ∧
          D.q0 + D.q1 ≤ ⌈4096 * (qGen : ℝ) * (Qsig : ℝ) ^ 4 / S.alpha ^ 4⌉₊ + S.qDec ∧
          S.alpha - 1 / 2 - δ - 2 * (2 * (S.qEnc : ℝ) + S.qDec) * Real.sqrt δ ≤ S.adv D ∧
          47 / 64 * S.alpha - 1 / 2 ≤ S.adv D)) ∧
    (∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] (ℓ μ : ℕ → ℕ)
      (S : ∀ n, QPKE1 (X n) (ℓ n) (μ n)) (qGen : ℕ → ℕ) (ϵc : ℕ → ℝ),
      (∀ n, (S n).GenQueriesLe (qGen n)) → PolyBounded qGen →
      PolyBounded (fun n => (S n).qEnc) → PolyBounded (fun n => (S n).qDec) → PolyBounded μ →
      Negligible ϵc → (∀ n, 1 - ϵc n ≤ (S n).alpha) →
      (∀ p : Polynomial ℕ, (∀ n : ℕ, 0 < p.eval n) →
        ∃ D : ∀ n, INDAttacker (S n), PolyBounded (fun n => (D n).q0 + (D n).q1) ∧
          ∃ ν : ℕ → ℝ, Negligible ν ∧
            ∀ n : ℕ, 1 / 2 - 1 / ((p.eval n : ℕ) : ℝ) - ν n ≤ (S n).adv (D n)) ∧
      ¬ (∀ D : ∀ n, INDAttacker (S n), PolyBounded (fun n => (D n).q0 + (D n).q1) →
          Negligible (fun n => (S n).adv (D n)))) ∧
    (∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ} (S : QPKE1c X ℓ μ) (qGen qDec : ℕ),
      S.GenQueriesLe qGen → S.DecQueriesLe qDec →
      (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ D : CINDAttacker S.PK S.Ct X ℓ μ,
        D.QueriesLe (⌈(qGen : ℝ) / δ ^ 2⌉₊ + qDec) ∧
        S.alpha - 1 / 2 - δ - 2 * (2 * (S.qEnc : ℝ) + qDec) * Real.sqrt δ ≤ S.advC D) ∧
      (0 < S.alpha →
        let Qsig : ℕ := max 1 (2 * S.qEnc + qDec)
        let δ : ℝ := (S.alpha / (8 * Qsig)) ^ 2
        ∃ D : CINDAttacker S.PK S.Ct X ℓ μ,
          D.QueriesLe (⌈(qGen : ℝ) / δ ^ 2⌉₊ + qDec) ∧
          D.QueriesLe (⌈4096 * (qGen : ℝ) * (Qsig : ℝ) ^ 4 / S.alpha ^ 4⌉₊ + qDec) ∧
          S.alpha - 1 / 2 - δ - 2 * (2 * (S.qEnc : ℝ) + qDec) * Real.sqrt δ ≤ S.advC D ∧
          47 / 64 * S.alpha - 1 / 2 ≤ S.advC D)) ∧
    (∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] (ℓ μ : ℕ → ℕ)
      (S : ∀ n, QPKE1c (X n) (ℓ n) (μ n)) (qGen qDec : ℕ → ℕ) (ϵc : ℕ → ℝ),
      (∀ n, (S n).GenQueriesLe (qGen n)) → (∀ n, (S n).DecQueriesLe (qDec n)) →
      PolyBounded qGen → PolyBounded (fun n => (S n).qEnc) → PolyBounded qDec →
      PolyBounded μ → Negligible ϵc → (∀ n, 1 - ϵc n ≤ (S n).alpha) →
      (∀ p : Polynomial ℕ, (∀ n : ℕ, 0 < p.eval n) →
        ∃ (D : ∀ n, CINDAttacker (S n).PK (S n).Ct (X n) (ℓ n) (μ n)) (N : ℕ → ℕ),
          (∀ n, (D n).QueriesLe (N n)) ∧ PolyBounded N ∧
          ∃ ν : ℕ → ℝ, Negligible ν ∧
            ∀ n : ℕ, 1 / 2 - 1 / ((p.eval n : ℕ) : ℝ) - ν n ≤ (S n).advC (D n)) ∧
      ¬ (∀ (D : ∀ n, CINDAttacker (S n).PK (S n).Ct (X n) (ℓ n) (μ n)) (N : ℕ → ℕ),
          (∀ n, (D n).QueriesLe (N n)) → PolyBounded N →
          Negligible (fun n => (S n).advC (D n)))) := by sorry

end KAQROM.Supplement
