-- Prove2me | Theorems.Thm_KAQROM_Supplement_theorem_6_2
-- name    : KAQROM.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:54:14.213608+00:00
-- url     : https://prove2.me/theorems/09b56e0c-235b-4a21-abbb-7090d5e7daa9
-- title:
--   Theorem 6.2 — a passive classical attacker with $N_1+N_2$ queries recovers Bob's key in every Bob-first two-message protocol w.p. $\ge\alpha-2\Delta_2$
-- statement:
--   Let $\Pi^{qb}=(B_1,A,B_2)$ be a Bob-first two-message protocol (Definition 6.1). Bob makes at most $q_{B,1}$ and $q_{B,2}$ quantum queries in his two stages, Alice makes at most $q_A$ classical queries, and $\alpha=\alpha_{\Pi^{qb}}$. For $0<\beta,\gamma,\eta_1,\eta_2<1$ set
--   $$
--   N_1=\Bigl\lceil\frac{q_{B,1}}{\eta_1\beta}\Bigr\rceil,\qquad N_2=\Bigl\lceil\frac{q_A}{\eta_2\gamma}\Bigr\rceil,\qquad \Delta_2=\eta_1+\eta_2+2(q_A+N_2)\sqrt\beta+2q_{B,2}\sqrt\gamma .
--   $$
--   Then there is a computationally unbounded passive classical attacker $E$ with the following properties:
--
--   1. it receives $(M_1,M_2)$ after the honest execution and makes at most $N_1+N_2$ classical oracle queries;
--   2. it computes its key guess $K^*$ deterministically from the answers it received, and
--   $$
--   \mathrm{Adv}^{\mathrm{KR}}_{\Pi^{qb},E}\ \ge\ \alpha-2\Delta_2 ;
--   $$
--   3. if the protocol has completeness error $\epsilon_c$, i.e. $\alpha\ge1-\epsilon_c$, then the advantage is at least $1-\epsilon_c-2\Delta_2$.
--
--   This is the two-message attack on protocols in which only Bob queries quantumly. It is the basis of the attack on QPKE with classical-query encryption (Theorem 7.2).
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
--   - encoding: Alice's query bound q_A → a parameter qA with the hypothesis AQueriesLe qA; reason: q_A is any worst-case bound; N₂ and ∆₂ use it as printed
--   - generalization: worst-case query bound over every branch → bound required only on branches of positive probability; reason: zero-probability branches change no probability; the paper's bound implies the hypothesis
--   - encoding: B2^H(S_B, M2) → B2 chosen by (M1, M2); reason: Bob knows the message he sent; equivalently M1 is kept in S_B
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 6.2, p.46; Definition 6.1, pp.45–46

import Mathlib
import Definitions.Def_KAQROM_Supplement_DetAttacker
import Definitions.Def_KAQROM_Supplement_BobFirst

namespace KAQROM.Supplement

open KAQROM

/-- **Theorem 6.2 (Two-message attack with quantum Bob).** For `0 < β, γ, η₁, η₂ < 1` set
`N₁ := ⌈q_{B,1}/(η₁β)⌉`, `N₂ := ⌈q_A/(η₂γ)⌉` and
`∆₂ := η₁ + η₂ + 2(q_A + N₂)√β + 2q_{B,2}√γ`. Every protocol `Π^{qb}` of Definition 6.1 has a
computationally unbounded passive classical attacker `E` that makes at most `N₁ + N₂` classical
oracle queries and satisfies `Adv^{KR}_{Π^{qb},E} ≥ α − 2∆₂`; it computes `K∗` deterministically
from its recorded view. If the protocol has completeness error `ϵ_c`, the advantage is at least
`1 − ϵ_c − 2∆₂`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 6.2, p.46.

**Formalization Note.** `qA` is any worst-case bound on Alice's classical queries
(`P.AQueriesLe qA`); `q_{B,1}`, `q_{B,2}` are the query rounds of Bob's stages. The attacker is a
deterministic classical-query algorithm on the transcript `(M₁, M₂)` (`DetAttacker`): its queries
and its key guess are functions of the transcript and the answers received, which is what
"passive", "classical" and "computes `K∗` deterministically from their recorded view" require; its
query bound holds on every oracle and every transcript. -/
theorem theorem_6_2 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : BobFirst X ℓ Msg K) (qA : ℕ) (hqA : P.AQueriesLe qA)
    (β γ η₁ η₂ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη₁0 : 0 < η₁)
    (hη₁1 : η₁ < 1) (hη₂0 : 0 < η₂) (hη₂1 : η₂ < 1) :
    let N₁ : ℕ := ⌈(P.qB1 : ℝ) / (η₁ * β)⌉₊
    let N₂ : ℕ := ⌈(qA : ℝ) / (η₂ * γ)⌉₊
    let Δ₂ : ℝ := η₁ + η₂ + 2 * ((qA : ℝ) + N₂) * Real.sqrt β + 2 * (P.qB2 : ℝ) * Real.sqrt γ
    ∃ E : DetAttacker (Msg × Msg) X ℓ (Option K),
      E.QueriesLe (N₁ + N₂) ∧
      P.alpha - 2 * Δ₂ ≤ P.advKR E ∧
      ∀ ϵc : ℝ, 1 - ϵc ≤ P.alpha → 1 - ϵc - 2 * Δ₂ ≤ P.advKR E := by sorry

end KAQROM.Supplement
