-- Prove2me | Theorems.Thm_KAQROM_eq_7
-- name    : KAQROM.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:54.305943+00:00
-- url     : https://prove2.me/theorems/b1722c58-aec8-4ffc-a032-770cbcc3893f
-- title:
--   Display (7) — $|\Pr[J_4]-\Pr[J_5]|\le\eta$, and $J_5$ is the interception attack of Definition 5.13
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10, let $0<\eta<1/100$, and let the learner have the properties of Lemma 5.11. For the hybrids built from this learner,
--   $$
--   \bigl|\Pr[J_4\text{ succeeds}]-\Pr[J_5\text{ succeeds}]\bigr|\le\eta,
--   $$
--   and hybrid $J_5$ is precisely an online interception experiment: if the learner makes at most $Q$ queries, there is an attacker $E$ in the class of Definition 3.11 (Definition 5.13: Eve records the messages, runs the learner on the complete transcript, prepares $(T'_A,S'_A)\leftarrow\omega^A_{m,h}$, and on receiving $\Psi$ runs $\mathcal A^{H[T'_A]}_{\mathsf{fin}}(m,S'_A,\Psi)$, or outputs $\bot$ if the learner aborted) that makes at most $Q$ classical queries during the prefix and $q_{A,\mathsf{fin}}$ quantum queries after receiving $\Psi$, with
--   $$
--   \mathrm{Adv}^{\mathsf{IntKR},\mathrm{mr}}_{\Pi^{\mathrm{mr}},E}=\Pr[J_5\text{ succeeds}] .
--   $$
--
--   This closes the hybrid argument: $J_5$ is the real attack.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - generalization: the learner $\mathsf{Learn}^{\mathsf{BM}}_\eta$ of Lemma 5.11 and the hybrids built from it → every prefix learner (a decision tree on the transcript that outputs its learned pairs or aborts, `PrefixLearner`) with the properties of Lemma 5.11 (`IsBMPrefixLearner`) and the hybrids built from it; reason: the proof uses only those properties; the learner of Lemma 5.11 (as stated in `lemma_5_11`) is an instance
--   - encoding: the hybrid experiments $J_1$–$J_5$ and $\Pr[J_i\text{ succeeds}]$ → explicit success probabilities: sums over oracles and prefix branches ($J_1$, $J_5$), and $\sum_{(m,h)}\pi(m,h)s_i(m,h)$ with $s_i$ computed from the blocks of $\omega^A_{m,h}$, $\omega^B_{m,h}$ and the uniform $\hat H$ ($J_2$–$J_4$); a learner abort is failure; reason: the paper's own decomposition of each hybrid (pp.39–42)
--   - reading: "Hybrid $J_5$ is precisely $\mathsf{IntKR}^{\mathrm{mr}}_{\Pi^{\mathrm{mr}},\mathcal E_\eta}$" with $\mathcal E_\eta$ of Definition 5.13 and "The query bound follows directly from Lemma 5.11 and Definition 5.13" → for every worst-case bound $Q$ on the learner's queries there is an attacker of Definition 3.11 with at most $Q$ prefix queries, $q_{A,\mathsf{fin}}$ final queries and advantage $\Pr[J_5]$; reason: $\mathcal E_\eta$ is built from the learner, which Lemma 5.11 gives only by existence; a query to $H[T'_A]$ costs one query to $H$ (p.41)
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of Theorem 5.14, display (7) and "Hybrid J5 is precisely IntKR", p.42; Definition 5.13, p.37; the query-bound sentence, p.42

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_Attacker
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_IsBMPrefixLearner
import Definitions.Def_KAQROM_Protocol_J1

namespace KAQROM

/-- **Display (7) and "Hybrid J5 is precisely IntKR^{mr}_{Π^{mr},E_η}"** in the hybrid argument
for Theorem 5.14. Fix `0 < η < 1/100` and a prefix learner with the properties of Lemma 5.11.
Then `|Pr[J4 succeeds] − Pr[J5 succeeds]| ≤ η`, and J5 is an online interception experiment:
if the learner makes at most `Q` queries, there is an attacker of Definition 3.11 (Definition 5.13:
Eve records the messages, runs the learner on the complete transcript, prepares
`(T'_A, S'_A) ← ω^A_{m,h}`, and on receiving `Ψ` runs `A_fin^{H[T'_A]}(m, S'_A, Ψ)`, or outputs `⊥`
on abort) making at most `Q` classical prefix queries and `q_{A,fin}` queries after `Ψ`, whose
advantage is `Pr[J5 succeeds]`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of Theorem 5.14, display (7) and the sentence after it, p.42; Definition 5.13,
p.37; "The query bound follows directly from Lemma 5.11 and Definition 5.13", p.42.

**Formalization Note.** The attacker of Definition 5.13 is stated by existence: it is built from
the learner, and a query to `H[T'_A]` costs one query to `H` (reversible membership test in the
known transcript, p.41). -/
theorem eq_7 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 100)
    (L : PrefixLearner (Fin P.n → Msg) X ℓ) (hL : IsBMPrefixLearner P η L) :
    |P.J4 L - P.J5 L| ≤ η ∧
      ∀ Q : ℕ, (∀ (H : Oracle X ℓ) (m : Fin P.n → Msg), (L.learned H m).length ≤ Q) →
        ∃ E : Attacker P, E.PrefixQueriesLe Q ∧ E.qE = P.qAfin ∧ E.advantage = P.J5 L := by sorry

end KAQROM
