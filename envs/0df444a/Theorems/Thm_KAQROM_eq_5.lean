-- Prove2me | Theorems.Thm_KAQROM_eq_5
-- name    : KAQROM.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:52.167714+00:00
-- url     : https://prove2.me/theorems/bc963650-c4de-4ac4-b295-24ca3dd8ea4d
-- title:
--   Display (5) — $|\Pr[J_0]-\Pr[J_1]|\le\eta$: inserting the learner costs at most its abort probability
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10, let $0<\eta<1/100$, and let the learner have the properties of Lemma 5.11 (`IsBMPrefixLearner`). For the hybrids of the proof of Theorem 5.14 built from this learner,
--   $$\bigl|\Pr[J_0\text{ succeeds}]-\Pr[J_1\text{ succeeds}]\bigr|\le\eta,$$ where $J_0$ is the honest execution, so that $\Pr[J_0\text{ succeeds}]=\alpha$, and $J_1$ additionally runs the learner on the complete prefix transcript and counts an abort as failure.
--
--   This is one step of the hybrid argument that proves Theorem 5.14; success of a hybrid means that its two recorded keys agree and are not $\bot$.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - generalization: the learner $\mathsf{Learn}^{\mathsf{BM}}_\eta$ of Lemma 5.11 and the hybrids built from it → every prefix learner (a decision tree on the transcript that outputs its learned pairs or aborts, `PrefixLearner`) with the properties of Lemma 5.11 (`IsBMPrefixLearner`) and the hybrids built from it; reason: the proof uses only those properties; the learner of Lemma 5.11 (as stated in `lemma_5_11`) is an instance
--   - encoding: the hybrid experiments $J_1$–$J_5$ and $\Pr[J_i\text{ succeeds}]$ → explicit success probabilities: sums over oracles and prefix branches ($J_1$, $J_5$), and $\sum_{(m,h)}\pi(m,h)s_i(m,h)$ with $s_i$ computed from the blocks of $\omega^A_{m,h}$, $\omega^B_{m,h}$ and the uniform $\hat H$ ($J_2$–$J_4$); a learner abort is failure; reason: the paper's own decomposition of each hybrid (pp.39–42)
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of Theorem 5.14, display (5), p.38

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_IsBMPrefixLearner
import Definitions.Def_KAQROM_Protocol_J1

namespace KAQROM

/-- **Display (5)** in the hybrid argument for Theorem 5.14. Fix `0 < η < 1/100`. For every prefix
learner with the properties of Lemma 5.11, the hybrids built from it satisfy `|Pr[J0 succeeds] − Pr[J1 succeeds]| ≤ η`, where `Pr[J0 succeeds] = α` (J0 is the honest execution).

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of Theorem 5.14, display (5), p.38.

**Formalization Note.** The paper's hybrids use the learner of Lemma 5.11; the statement holds for
every learner with that lemma's properties (`IsBMPrefixLearner`), which includes it. Success of a
hybrid is `K* = K_B ≠ ⊥` (both keys `some k`), and a learner abort counts as failure. -/
theorem eq_5 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 100)
    (L : PrefixLearner (Fin P.n → Msg) X ℓ) (hL : IsBMPrefixLearner P η L) :
    |P.alpha - P.J1 L| ≤ η := by sorry

end KAQROM
