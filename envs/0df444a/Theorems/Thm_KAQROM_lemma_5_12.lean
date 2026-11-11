-- Prove2me | Theorems.Thm_KAQROM_lemma_5_12
-- name    : KAQROM.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:30.394508+00:00
-- url     : https://prove2.me/theorems/88558cf3-4ccc-4bf2-981f-21ff436d09a7
-- title:
--   Lemma 5.12 — conditioned prefix resampling: $\tfrac12\|\Omega_{m,h}-\tilde\Omega_{m,h}\|_1\le\eta$
-- statement:
--   Let $\Pi^{\mathrm{mr}}$ satisfy Definition 3.10, let $0<\eta<1/100$, and let the learner have the properties of Lemma 5.11. Fix a reachable pair $(m,h)$ and consider the experiment that independently prepares $(T'_A,S'_A)\leftarrow\omega^A_{m,h}$ and $(T'_B,S'_B)\leftarrow\omega^B_{m,h}$, samples $H_0\leftarrow\mathrm{Unif}(\mathcal H(h,T'_B))$ and sets $\tilde H=H_0[T'_A]$. Let $\tilde\Omega_{m,h}$ be the resulting state on $HT'_AS'_AT'_BS'_B$, with $H$ holding $\tilde H$. Then
--   $$
--   \tfrac12\bigl\|\Omega_{m,h}-\tilde\Omega_{m,h}\bigr\|_1\ \le\ \tfrac12\bigl\|\omega^{AB}_{m,h}-\omega^A_{m,h}\otimes\omega^B_{m,h}\bigr\|_1\ \le\ \eta .
--   $$
--
--   The resampled state is what the attacker can prepare from $(m,h)$ alone; the lemma says it is close to the real conditioned state, oracle included.
--
--   Differences from the source:
--   - encoding: a security parameter λ with inputs $1^\lambda$ → one fixed λ, $1^\lambda$ arguments dropped; reason: every statement of §5.2 is at one fixed λ with explicit constants
--   - generalization: $X=\{0,1\}^{n(\lambda)}$, $Y=\{0,1\}^{\ell(\lambda)}$ with $\ell(\lambda)\ge1$ → any finite type $X$ and any $\ell\in\mathbb N$, including $\ell=0$ (with $Y=\{0,1\}^\ell$ kept as bit strings, XOR as addition in $\mathbb Z_2^\ell$); reason: $n(\lambda)$, $\ell(\lambda)$ enter only through the sets $X$, $Y$ and no argument uses $\ell\ge1$; $X=\{0,1\}^n$, $\ell\ge1$ is an instance
--   - encoding: quantum oracle algorithms making at most $q$ queries, alternating oracle-independent operations with $U_H$ → exactly $q$ query rounds interleaved with arbitrary channels (Kraus families), then a measurement; reason: a query on the response state $|+\rangle^{\otimes\ell}$ is idle, so any algorithm pads to exactly $q$; parties are computationally unbounded (Stinespring)
--   - encoding: classical oracle access in the prefix (Definition 3.1); stages $A_i$, $B_i$ with residual registers → each stage is $D$ query steps and one message step, each a quantum instrument selected by the party's classical record (messages so far, own query–answer list, step index); a step with outcome none makes no query; one fixed register per party; reason: this is Definition 3.1's classical access (answers returned classically and recorded); idle steps and a large enough register pad any finite stage
--   - encoding: keys in $K_\lambda\cup\{\bot\}$ → `Option K` with ⊥ = `none`; reason: same values
--   - encoding: $\omega^{AB}_{m,h}$ defined through the exact classical simulation and the channels $\Phi_A\otimes\Phi_B$ → $\omega^{AB}_{m,h}$ defined as the $T_AS_AT_BS_B$-marginal of $\Omega_{m,h}$, with $\omega^A$, $\omega^B$ its marginals; reason: the paper states the two are equal ("Since the simulation is exact", p.33)
--   - encoding: $\tfrac12\|\cdot\|_1$ on states classical on $(H,T_A,T_B)$ → half the sum of the trace norms of the blocks; reason: exact for block-diagonal operators
--   - generalization: the learner $\mathsf{Learn}^{\mathsf{BM}}_\eta$ of Lemma 5.11 and the hybrids built from it → every prefix learner (a decision tree on the transcript that outputs its learned pairs or aborts, `PrefixLearner`) with the properties of Lemma 5.11 (`IsBMPrefixLearner`) and the hybrids built from it; reason: the proof uses only those properties; the learner of Lemma 5.11 (as stated in `lemma_5_11`) is an instance
--   - generalization: "$\tfrac12\|\Omega_{m,h}-\tilde\Omega_{m,h}\|_1\le\eta$" → the chain $\tfrac12\|\Omega-\tilde\Omega\|_1\le\tfrac12\|\omega^{AB}-\omega^A\otimes\omega^B\|_1\le\eta$ (both inequalities); reason: the second conjunct is the printed claim; the first is the inequality the proof establishes
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.12 and the last display of its proof, pp.36–37

import Mathlib
import Definitions.Def_KAQROM_CQ
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_Protocol_Omega
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_IsBMPrefixLearner

namespace KAQROM

/-- **Lemma 5.12 (Conditioned prefix resampling).** Fix `0 < η < 1/100` and a prefix learner with
the properties of Lemma 5.11, and fix a reachable pair `(m, h)`. Let `Ω̃_{m,h}` be the state on
`H T'_A S'_A T'_B S'_B` obtained by independently preparing `(T'_A, S'_A) ← ω^A_{m,h}` and
`(T'_B, S'_B) ← ω^B_{m,h}`, sampling `H₀ ← Unif(ℋ(h, T'_B))` and setting `H̃ = H₀[T'_A]`, with `H`
holding `H̃`. Then `½‖Ω_{m,h} − Ω̃_{m,h}‖₁ ≤ ½‖ω^{AB}_{m,h} − ω^A_{m,h} ⊗ ω^B_{m,h}‖₁ ≤ η`; the
second inequality is Lemma 5.11 (ii), and the printed claim is `½‖Ω_{m,h} − Ω̃_{m,h}‖₁ ≤ η`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.12 and the
last display of its proof, pp.36–37.

**Formalization Note.** "Reachable" is with respect to the learner (`probReach > 0`); the lemma is
stated for every learner with the properties of Lemma 5.11, which includes the one of that lemma. -/
theorem lemma_5_12 {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
    [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < 1 / 100) (L : PrefixLearner (Fin P.n → Msg) X ℓ) (hL : IsBMPrefixLearner P η L)
    (m : Fin P.n → Msg) (h : PartialOracle X ℓ) (hreach : 0 < P.probReach L m h) :
    cqTraceDist (P.Omega m h) (P.OmegaTilde m h) ≤
        cqTraceDist (P.omegaAB m h) (cqProd (P.omegaA m h) (P.omegaB m h)) ∧
      cqTraceDist (P.Omega m h) (P.OmegaTilde m h) ≤ η := by sorry

end KAQROM
