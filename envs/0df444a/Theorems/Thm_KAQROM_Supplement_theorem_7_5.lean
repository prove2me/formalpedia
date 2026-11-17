-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_7_5
-- name    : KAQROM.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:57:53.076199+00:00
-- url     : https://prove2.me/theorems/78aa700a-3cb6-4bfb-8053-b7c87199e268
-- title:
--   Theorem 7.5 — constant-round binary-output tests of non-commutation are not query-bounded sound: a commuting-observable prover with polynomially many queries accepts w.p. $\ge\alpha_\Pi-\xi$
-- statement:
--   Let $\Pi$ be a binary-output test of non-commutation in the QROM of the form on p.76, with a fixed number $r$ of rounds. It has a classical verifier with classical oracle access and a quantum prover; the verifier sends a challenge bit $c$, the prover measures a binary observable $P_c$ and answers $a$, and the verifier accepts iff $V^H_{\mathrm{Ver}}(st,a)=1$. This predicate may accept either, both, or neither answer. Let $\alpha_\Pi$ be the honest acceptance probability and $Q$ a bound on the honest query complexity.
--
--   1. For every $r$ there are constants $C_r>0$ and $d_r$ with the following property. For every $r$-round test, every bound $Q$ and every $\xi\in(0,1)$ there is a computationally unbounded quantum prover whose final observables commute for every oracle $H$. It makes at most $C_r(Q+1)^{d_r}/\xi^{d_r}$ queries, and its acceptance probability is at least
--   $$
--   \alpha_\Pi-\xi .
--   $$
--   Applied at $\xi=\xi(\lambda)$, this gives such a prover for every inverse-polynomial $\xi(\lambda)\in(0,1)$, with query complexity polynomial in the honest query bound and $1/\xi$ and degree depending only on $r$.
--   2. Consequently, no family of such tests with polynomial honest query complexity has query-bounded soundness with $\alpha_\Pi(\lambda)-\beta(\lambda)\ge1/\mathrm{poly}(\lambda)$. Soundness with bound $\beta$ would require every prover with polynomially many queries and commuting final observables to be accepted with probability at most $\beta(\lambda)+\mathrm{negl}(\lambda)$.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - encoding: poly(λ), negl(λ), 'for every polynomial p' → λ-indexed families; the published PolyBounded and Negligible; p : Polynomial ℕ with positive values; reason: standard asymptotic notions; a positive polynomial is bounded by some (λ+2)^c
--   - reading: fix a constant number of rounds; for every inverse-polynomial ξ(λ) ∈ (0,1) a prover with query complexity polynomial in the honest bound and 1/ξ, degree depending only on the rounds → for every r there are C_r > 0 and d_r such that for every r-round test, every honest bound Q and every ξ ∈ (0,1) there is a commuting prover with at most C_r (Q+1)^{d_r}/ξ^{d_r} queries; reason: the per-λ, every-ξ form implies the inverse-polynomial statement; it is the stronger reading
--   - encoding: a constant number of rounds → the number r of verifier stages of a preparation phase laid out as in Definition 6.10, followed by the challenge round; reason: the proof of Theorem 7.5 treats the test as a Definition 6.10 protocol
--   - generalization: the honest prover applies a binary observable P_c → any binary-outcome quantum oracle algorithm; reason: observables are the projective case; the class of tests is larger
--   - reading: commuting final observables P̃^H_0 P̃^H_1 = P̃^H_1 P̃^H_0 for every H → for every H and transcript, each final measurement is projective and its observables E(0) − E(1) commute; reason: an observable is a projective binary measurement; fixing H and the transcript determines it
--   - generalization: α_Π(λ) − β(λ) ≥ 1/poly(λ) → 1/p(λ) ≤ α_Π(λ) − β(λ) for all λ ≥ λ₀; reason: a weaker hypothesis; it implies the printed one
--   - encoding: query-bounded soundness with bound β → every cheating-prover family with polynomially bounded queries and commuting final observables has acceptance ≤ β(λ) + ν(λ) for a negligible ν; reason: the definition on p.76
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.5, p.76; §7.4 (syntax, soundness, pointwise commutation), p.76

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_KAQROM_Supplement_ToNC

namespace KAQROM.Supplement

open KAQROM
open PPADSIS.SubexpSIS

/-- **Theorem 7.5 (Impossibility of constant-round ToNC).** Fix a constant number of rounds, and
let `Π` be a binary-output test of the form of p.76 with polynomial honest query complexity. For
every inverse-polynomial function `ξ(λ) ∈ (0,1)` there is a computationally unbounded quantum
prover with commuting final observables whose acceptance probability is at least `α_Π(λ) − ξ(λ)`.
Its query complexity is polynomial in the honest query bound and `1/ξ`, with degree depending only
on the fixed number of rounds. Consequently, no such test has query-bounded soundness with
`α_Π(λ) − β(λ) ≥ 1/poly(λ)`. The verification predicate may accept either, both, or neither of the
two possible answers.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.5, p.76
(the syntax, soundness and pointwise commutation on p.76).

**Formalization Note.** First conjunct (quantitative core, per `λ`): for each number `r` of rounds
there are constants `C_r > 0`, `d_r` such that for every `r`-round test, every bound `Q` on its
honest query complexity and every `ξ ∈ (0,1)` there is a cheating prover with commuting final
observables, at most `C_r (Q+1)^{d_r} / ξ^{d_r}` queries and acceptance `≥ α_Π − ξ`; applied at
`ξ = ξ(λ)` this gives the printed claim for every inverse-polynomial `ξ`. Second conjunct
(soundness): for every family of `r`-round tests with polynomially bounded honest query
complexity and every `β`, if `α_Π(λ) − β(λ) ≥ 1/p(λ)` for a positive polynomial `p` and all large
`λ`, then the family is not query-bounded sound with bound `β` (sound: every cheating-prover family
with polynomially many queries and commuting final observables accepts with probability at most
`β(λ) + negl(λ)`). The verification predicate is an arbitrary deterministic classical-query
algorithm. -/
theorem theorem_7_5 :
    (∀ r : ℕ, ∃ (Cr : ℝ) (dr : ℕ), 0 < Cr ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg St : Type} [Fintype Msg]
        [DecidableEq Msg] [Fintype St] (T : ToNC X ℓ Msg St), T.r = r →
        ∀ Q : ℕ, T.HonestQueriesLe Q → ∀ ξ : ℝ, 0 < ξ → ξ < 1 →
          ∃ C : CheatProver T, C.HasCommutingObservables ∧
            (C.queries : ℝ) ≤ Cr * ((Q : ℝ) + 1) ^ dr / ξ ^ dr ∧
            T.alpha - ξ ≤ T.acc C) ∧
    (∀ (r : ℕ) (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] (ℓ : ℕ → ℕ)
      (Msg St : ℕ → Type) [∀ n, Fintype (Msg n)] [∀ n, DecidableEq (Msg n)]
      [∀ n, Fintype (St n)] (T : ∀ n, ToNC (X n) (ℓ n) (Msg n) (St n)), (∀ n, (T n).r = r) →
      ∀ Q : ℕ → ℕ, (∀ n, (T n).HonestQueriesLe (Q n)) → PolyBounded Q →
      ∀ (β : ℕ → ℝ) (p : Polynomial ℕ), (∀ n : ℕ, 0 < p.eval n) →
        (∃ n₀ : ℕ, ∀ n ≥ n₀, 1 / ((p.eval n : ℕ) : ℝ) ≤ (T n).alpha - β n) →
        ¬ (∀ C : ∀ n, CheatProver (T n), PolyBounded (fun n => (C n).queries) →
            (∀ n, (C n).HasCommutingObservables) →
            ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, (T n).acc (C n) ≤ β n + ν n)) := by sorry

end KAQROM.Supplement
