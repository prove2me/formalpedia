-- Prove2me | Theorems.Thm_KAQROM_lemma_5_16
-- name    : KAQROM.lemma_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:21.839257+00:00
-- url     : https://prove2.me/theorems/ff1572be-76c1-42d5-95f1-e0cb52695e1e
-- title:
--   Lemma 5.16 — $J_3$ to $J_4$: $|\Pr[J_3]-\Pr[J_4]|\le 2(q_{B,\mathsf q}+q_{A,\mathsf{fin}})\sqrt\eta$
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10, let $0<\eta<1/100$, and let the learner have the properties of Lemma 5.11 (`IsBMPrefixLearner`). For the hybrids of the proof of Theorem 5.14 built from this learner,
--   $$\bigl|\Pr[J_3\text{ succeeds}]-\Pr[J_4\text{ succeeds}]\bigr|\le 2(q_{B,\mathsf q}+q_{A,\mathsf{fin}})\sqrt\eta,$$ where $J_4$ gives Bob the oracle $H^B=\hat H[T^B_A]$ programmed by an independent second Alice view and Alice's final stage $H^E=H^B[T^E_A]$.
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
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.16, p.41

import Mathlib
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_IsBMPrefixLearner
import Definitions.Def_KAQROM_Protocol_J1

namespace KAQROM

/-- **Lemma 5.16 (J3 to J4)** in the hybrid argument for Theorem 5.14. Fix `0 < η < 1/100`. For every prefix
learner with the properties of Lemma 5.11, the hybrids built from it satisfy `|Pr[J3 succeeds] − Pr[J4 succeeds]| ≤ 2(q_{B,q} + q_{A,fin})√η`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.16, p.41.

**Formalization Note.** The paper's hybrids use the learner of Lemma 5.11; the statement holds for
every learner with that lemma's properties (`IsBMPrefixLearner`), which includes it. Success of a
hybrid is `K* = K_B ≠ ⊥` (both keys `some k`), and a learner abort counts as failure. -/
theorem lemma_5_16 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1 / 100)
    (L : PrefixLearner (Fin P.n → Msg) X ℓ) (hL : IsBMPrefixLearner P η L) :
    |P.J3 L - P.J4 L| ≤ 2 * ((P.qBq : ℝ) + P.qAfin) * Real.sqrt η := by sorry

end KAQROM
