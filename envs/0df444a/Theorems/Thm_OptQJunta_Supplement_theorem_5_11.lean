-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_5_11
-- name    : OptQJunta.Supplement.theorem_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:19:35.482221+00:00
-- url     : https://prove2.me/theorems/93f8b947-af2c-43cb-9918-262a9ecf536a
-- title:
--   Theorem 5.11 — exact classicalization of forward queries on the phase-masked ensemble $\mathbb U(p)$
-- statement:
--   Fix integers $M\ge2$, $r\ge1$ and $q\ge0$, and let $n=r+M$. Let $\mathcal A$ be a binary-output quantum algorithm, independent of the distribution $p$ that defines the ensemble $\mathbb U(p)$, that makes at most $q$ queries with forward-only access to an unknown $n$-qubit unitary. There is a function $F_{\mathcal A}:[M]^q\to[0,1]$, independent of $p$, such that for every $p\in\Delta([M])$,
--
--   $$
--   \mathbb E_{U_{f,g}\sim\mathbb U(p)}\big[\mathrm{Acc}_{\mathcal A}(U_{f,g})\big]=\mathbb E_{Y\sim p^{\otimes q}}\big[F_{\mathcal A}(Y)\big].
--   $$
--
--   Here $U_{f,g}$ is the phase-masked unitary of Definition 5.7, with $f(x)$ i.i.d. from $p$ and $g_x$ i.i.d. uniform on the unit circle, and $\mathrm{Acc}_{\mathcal A}(U)$ is the probability that $\mathcal A$ accepts.
--
--   The identity turns any forward-only tester on the ensemble into a classical $q$-sample tester, which reduces the lower bounds of Theorems 5.6 and 6.3 to Theorem 3.14.
--
--   **Formalization Note** $\mathcal A$ is a forward-only `SamplerAlg` on $r+M$ query qubits with $T\le q$ queries, an arbitrary finite workspace and start state, and output bit `true` for acceptance. $F$ is chosen before $p$. The ensemble average is the sum over $f$ weighted by $\prod_xp(f(x))$ of the normalized integral over $\theta\in[0,2\pi)^{2^r}$ with $g_x=e^{i\theta_x}$.
--
--   Differences from the source:
--   - encoding: a quantum query algorithm with ancillas, private randomness, intermediate measurements and adaptivity, counting the worst-case number of queries → the published OptQJunta.SamplerAlg on the n query qubits: oracle-independent unit start state and unitaries on Qubits n × W (W an arbitrary finite workspace), exactly T calls with a fixed pattern, final computational-basis measurement; reason: deferred measurement, purification of the randomness and padding with dummy queries give the same output law on every unitary; an adaptive choice between U and U† is simulated by the alternating pattern at twice the cost, which only rescales the absolute constant (same encoding as the base mission, paper.md decision 3)
--   - encoding: forward-only access: one query applies U → a SamplerAlg with every slot calling U (IsForwardOnly: dir i = false for all i); reason: §2.5.2, p.23
--   - encoding: U_{f,g} on qubits [r] (address) and r + j, j ∈ [M] (data) → Qubits (r + M) from 0: address qubit i at position i < r, data qubit j : Fin M at position r + j; reason: Lean indexing; same unitaries
--   - encoding: g_x i.i.d. Haar on the unit circle 𝕋 → g_x = e^{iθ_x}, θ uniform on [0, 2π)^{2^r}: (2π)^{−2^r} ∫ over the box; reason: the Haar law on 𝕋 is the law of e^{iθ} for θ uniform on [0, 2π) (p.65)
--   - encoding: Acc_𝒜(U), the acceptance probability of a binary-output algorithm → outputProb U out true; reason: output true = accept
--   - encoding: E_{Y∼p^{⊗q}}[F_𝒜(Y)] with F_𝒜 : [M]^q → [0, 1] → sampleAcc F p with IsTestFn F on Fin q → Fin M; reason: same expression; [M] is Fin M from 0
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 5.11, p.67 (Definition 5.7 and the ensemble 𝕌(p), p.65; §5.4.2, p.67)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg
import Definitions.Def_OptQJunta_Supplement_sampleAcc
import Definitions.Def_OptQJunta_Supplement_TestsJuntaU
import Definitions.Def_OptQJunta_Supplement_phaseMasked

namespace OptQJunta.Supplement

open QAlgorithms OptQJunta

/-- **Theorem 5.11** (Exact forward-query classicalization; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.67). Fix integers `M ≥ 2`,
`r ≥ 1`, and `q ≥ 0`, and let `n = r + M`. Let `𝒜` be a binary-output quantum algorithm, independent
of the distribution `p` that defines the ensemble `𝕌(p)`, that makes at most `q` queries with
forward-only access to an unknown `n`-qubit unitary. There is a function `F_𝒜 : [M]^q → [0, 1]`,
independent of `p`, such that for every `p ∈ Δ([M])`,
`E_{U_{f,g}∼𝕌(p)}[Acc_𝒜(U_{f,g})] = E_{Y∼p^{⊗q}}[F_𝒜(Y)]`.

**Formalization Note** `𝒜` is a forward-only `T`-query algorithm (`SamplerAlg` with every slot
calling `U`) with `T ≤ q`, an arbitrary finite workspace and start state; `Acc_𝒜(U)` is its probability
of output `true`. `F` is chosen before `p`. The ensemble average is `ensembleAvg` (Definition 5.7 and
§5.4.1, p.65). -/
theorem theorem_5_11 :
    ∀ (M r q : ℕ), 2 ≤ M → 1 ≤ r →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : SamplerAlg (Qubits (r + M)) W T)
        (out : Qubits (r + M) × W → Bool), IsForwardOnly A → T ≤ q →
        ∃ F : (Fin q → Fin M) → ℝ, IsTestFn F ∧
          ∀ p : Fin M → ℝ, IsDist p →
            ensembleAvg p (fun U => A.outputProb U out true) = sampleAcc F p := by sorry

end OptQJunta.Supplement
