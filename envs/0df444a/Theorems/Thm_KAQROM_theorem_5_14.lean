-- Prove2me | Theorems.Thm_KAQROM_theorem_5_14
-- name    : KAQROM.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:20.832205+00:00
-- url     : https://prove2.me/theorems/716c751e-0cd3-430c-9c2a-f922c44575ec
-- title:
--   Theorem 5.14 — multi-round attack: $\mathrm{Adv}\ge\alpha-3\eta-2(2q_{B,\mathsf q}+q_{A,\mathsf{fin}})\sqrt\eta$ with $\lceil4\cdot10^5\bar q_A\bar q_B/\eta^3\rceil$ prefix queries
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10 and let $\alpha=\alpha_{\Pi^{\mathrm{mr}}}$ be its valid agreement probability. For every $0<\eta<1/100$ there is an online interception attacker $\mathcal E_\eta$ (Definition 3.11) with
--   $$
--   \mathrm{Adv}^{\mathsf{IntKR},\mathrm{mr}}_{\Pi^{\mathrm{mr}},\mathcal E_\eta}\ \ge\ \alpha-3\eta-2(2q_{B,\mathsf q}+q_{A,\mathsf{fin}})\sqrt\eta ,
--   $$
--   which makes at most
--   $$
--   \Bigl\lceil\frac{4\cdot10^5\max\{1,q_{A,\mathrm{pre}}\}\max\{1,q_{B,\mathrm{pre}}\}}{\eta^3}\Bigr\rceil
--   $$
--   classical queries during the prefix and at most $q_{A,\mathsf{fin}}$ queries after receiving $\Psi$, in the worst case. Neither bound depends on the number $r$ of prefix rounds.
--
--   This is the paper's first main result: no key-agreement protocol whose prefix uses only classical queries and classical messages, followed by one possibly quantum message, is secure against attackers with polynomially more queries than the honest parties, even when the parties agree only with inverse-polynomial probability.
--
--   **Formalization Note** The statement holds for every protocol of Definition 3.10: any $r\ge1$, any finite registers and message sets, quantum residual states and a quantum message $\Psi$, quantum queries in both final stages.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - encoding: $q_{A,\mathrm{pre}} := \max|T_A|$, $q_{B,\mathrm{pre}} := \max|T_B|$ → the maximum over every oracle and every prefix branch of positive probability; reason: the paper's worst case over executions
--   - reading: "the attacker of Definition 5.13 satisfies" → there is an attacker in the class of Definition 3.11 satisfying the bounds; reason: Definition 5.13 uses $\mathsf{Learn}^{\mathsf{BM}}_\eta$ of Lemma 5.11, which is given only by existence
--   - reading: "It makes at most $\lceil\cdots\rceil+q_{A,\mathsf{fin}}$ random-oracle queries. The first term consists only of classical queries" → two worst-case bounds: at most $\lceil\cdots\rceil$ classical queries during the prefix (every oracle, every branch of positive probability) and at most $q_{A,\mathsf{fin}}$ query rounds after $\Psi$; reason: the second sentence assigns the first term to the classical queries; the two bounds sum to the printed total
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 5.14, p.38

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_Attacker

namespace KAQROM

/-- **Theorem 5.14 (Multi-round quantitative attack).** Let `Π^{mr}` satisfy Definition 3.10 and
let `α = α_{Π^{mr}}`. For every `0 < η < 1/100` there is an online interception attacker `E_η`
(Definition 3.11) with
`Adv^{IntKR,mr}_{Π^{mr},E_η} ≥ α − 3η − 2(2q_{B,q} + q_{A,fin})√η`,
which makes at most `⌈4·10⁵ max{1,q_{A,pre}} max{1,q_{B,pre}} / η³⌉` classical queries during the
prefix and at most `q_{A,fin}` (quantum) queries after receiving `Ψ`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 5.14,
p.38.

**Formalization Note.** "The attacker of Definition 5.13" is stated as "there is an attacker":
Definition 5.13 builds it from the learner of Lemma 5.11, which is itself given only by
existence. The query sentence is two worst-case bounds, one per phase (their sum is the printed
total, and the first term is classical by the attacker class). The number of prefix rounds `r`
does not occur in either bound. -/
theorem theorem_5_14 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < 1 / 100) :
    ∃ E : Attacker P,
      E.PrefixQueriesLe
        ⌈4 * 10 ^ 5 * ((max 1 P.qApre : ℕ) : ℝ) * ((max 1 P.qBpre : ℕ) : ℝ) / η ^ 3⌉₊ ∧
      E.qE ≤ P.qAfin ∧
      P.alpha - 3 * η - 2 * (2 * (P.qBq : ℝ) + P.qAfin) * Real.sqrt η ≤ E.advantage := by sorry

end KAQROM
