-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_5_2
-- name    : KAQROM.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:53:37.239011+00:00
-- url     : https://prove2.me/theorems/8055f202-d7a5-49d4-9c79-7ab0b3f8b755
-- title:
--   Theorem 5.2 — the reprogramming attacker $E_\delta$ breaks every two-message protocol: $\mathrm{Adv}\ge\alpha-\delta-2(2q_B+q_{A,2})\sqrt\delta$ with $\lceil q_{A,1}/\delta^2\rceil+q_{A,2}$ queries
-- statement:
--   Let $\Pi=(A_1,B,A_2)$ be a two-message key-agreement protocol with a classical first message (Definition 3.7). Alice's first stage has classical oracle access and records a transcript of length $|T_A|\le q_{A,1}$, Bob makes at most $q_B$ quantum queries, and Alice's final stage makes at most $q_{A,2}$. Let $\alpha=\alpha_\Pi$ be the valid agreement probability, and fix a total order $\prec$ on $X$. For every $0<\delta<1$, Eve's two-stage reprogramming attacker $E_\delta$ of Definition 5.1 satisfies
--   $$
--   \mathrm{Adv}^{\mathrm{IntKR}}_{\Pi,E_\delta}\ \ge\ \alpha-\delta-2(2q_B+q_{A,2})\sqrt\delta .
--   $$
--   It makes at most
--   $$
--   \Bigl\lceil \frac{q_{A,1}}{\delta^2}\Bigr\rceil+q_{A,2}
--   $$
--   random-oracle queries: at most $\lceil q_{A,1}/\delta^2\rceil$ classical queries in its learner and $q_{A,2}$ quantum queries in its second stage.
--
--   The theorem shows that a protocol whose first message is computed with classical queries only cannot be secure against interception, even with imperfect completeness. The constants are explicit.
--
--   Differences from the source:
--   - encoding: security parameter λ and inputs 1^λ → one fixed λ; 1^λ arguments dropped; reason: the quantitative statement is per λ
--   - generalization: X = {0,1}^{n(λ)}, Y = {0,1}^{ℓ(λ)} with n, ℓ polynomially bounded → X any finite type, Y = Fin ℓ → ZMod 2 for any ℓ (XOR is +); reason: no bound depends on n or ℓ; the statement specializes to X = {0,1}^n
--   - encoding: quantum oracle algorithm with at most q queries → exactly q query rounds interleaved with arbitrary channels (published KAQROM.QAlg); reason: a query on the response state |+⟩^ℓ acts as the identity, so idle queries pad; parties are computationally unbounded
--   - encoding: classical oracle access → query steps whose instruments are selected by the classical record (CStage / published KAQROM.PrefixParty); reason: queries and answers are classical, the residual state stays quantum; this is Definition 3.1's notion
--   - encoding: keys in K ∪ {⊥} → Option K with ⊥ = none; reason: Lean convention; same instances
--   - encoding: all-zero private registers, local state preparation and private randomness inside the algorithms → arbitrary oracle-independent initial density operators; reason: local preparation from the all-zero state gives exactly these
--   - encoding: a protocol Π = (A1, B, A2) of Definition 3.7 → the published KAQROM.Protocol with r = 1; reason: with r = 1 the prefix is Alice's single classical-query stage sending M1, Bq is B and Afin is A2; Bob has no prefix stage
--   - encoding: A2^H(S_A, Ψ) → Afin chosen by the public message M1 (and B by M1, as in the source); reason: Alice knows the message she sent, so M1 can be kept in S_A; every A2 not depending on M1 is an instance
--   - encoding: the protocol's worst-case bound q_{A,1} on |T_A| → any qA1 with P.qApre ≤ qA1, from which E_δ (N_max) is built; reason: q_{A,1} is any worst-case bound declared by the protocol
--   - encoding: a fixed total order ≺ on X → every bijection ord : X ≃ Fin |X|; reason: a total order on a finite set is such a bijection
--   - encoding: at most ⌈q_{A,1}/δ²⌉ + q_{A,2} random-oracle queries → the learner's query list has length ≤ ⌈qA1/δ²⌉ on every oracle and input; E_{δ,2} runs A2 with its qAfin query rounds to H[T'_A]; reason: the two bounds of Definition 5.1; each query to H[T'_A] is one query to H (p.26)
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 5.2, p.26; Definition 5.1, p.26; Algorithm 1, p.24

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_Supplement_learn

namespace KAQROM.Supplement

open KAQROM

/-- **Theorem 5.2.** Let `Π = (A₁, B, A₂)` be a protocol as in Definition 3.7 and `α = α_Π`. For
every `0 < δ < 1`, the attacker `E_δ` of Definition 5.1 satisfies
`Adv^{IntKR}_{Π,E_δ} ≥ α − δ − 2(2q_B + q_{A,2})√δ`. It makes at most `⌈q_{A,1}/δ²⌉ + q_{A,2}`
random-oracle queries.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 5.2, p.26.

**Formalization Note.** A Definition 3.7 protocol is the published `KAQROM.Protocol` with `r = 1`
(Alice's classical-query first stage, Bob's `qBq`-query stage `B` producing `Ψ` and `K_B`, Alice's
`qAfin`-query final stage `A₂`). `qA1` is any worst-case bound on `|T_A|` (`P.qApre ≤ qA1`); `E_δ`
is defined from it (`N_max = ⌈q_{A,1}/δ²⌉`). The statement holds for every total order `≺` on `X`
(`ord`). The query sentence is the two bounds of Definition 5.1: the learner's classical queries
are at most `⌈q_{A,1}/δ²⌉` on every oracle and input (first conjunct), and the second stage runs
`A₂` with its `qAfin` query rounds to `H[T'_A]`, each one query to `H` (built into `advEdelta`). -/
theorem theorem_5_2 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (hr : P.r = 1) (qA1 : ℕ)
    (hqA1 : P.qApre ≤ qA1) (ord : X ≃ Fin (Fintype.card X)) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    (∀ (H : Oracle X ℓ) (m : Fin P.n → Msg),
        (learn P qA1 δ ord H m).2.length ≤ ⌈(qA1 : ℝ) / δ ^ 2⌉₊) ∧
      P.alpha - δ - 2 * (2 * (P.qBq : ℝ) + P.qAfin) * Real.sqrt δ ≤ advEdelta P qA1 δ ord := by sorry

end KAQROM.Supplement
